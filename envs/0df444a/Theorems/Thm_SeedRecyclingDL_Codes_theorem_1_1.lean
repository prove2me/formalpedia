-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_theorem_1_1
-- name    : SeedRecyclingDL.Codes.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:03.829968+00:00
-- url     : https://prove2.me/theorems/4a2eab7a-be65-4f32-afc1-2ecdfde81ee5
-- title:
--   Theorem 1.1 — Explicit binary codes for mixed synchronization errors
-- statement:
--   For every fixed integer $t\ge2$, there are uniform finite deterministic setup, encoding, full-message decoding, and payload-decoding programs for two binary code families. For all sufficiently large $n$, their actual encoders are injective into $\{0,1\}^n$, and distinct codewords have disjoint radius-$t$ unrestricted DL balls, allowing any combination of insertions, deletions, substitutions, and adjacent transpositions.
--   $$\begin{aligned}
--   \text{bootstrapped: }n-\log_2|C_n|&\le2t\log_2 n+2t\log_2\log_2n+O_t(\log_2\log_2\log_2n),\
--   \text{greedy: }n-\log_2|C_n|&\le2t\log_2 n+2t\log_2\log_2n+O_t(1).
--   \end{aligned}$$
--   Bootstrapped setup costs $\operatorname{polylog}(n)$. Greedy setup costs $n^{6t+2+o(1)}$, including the explicit Appendix D.2 envelope $C_tn^{6t+2}(\log_2n)^{4t+1}$. Every positive exponent slack has a threshold with cost at most $n^{6t+2+\varepsilon}$.
--
--   In both variants, encoding and full-message decoding cost $O_t(n^{2t+2}\log_2^2n)$ bit operations. From every valid output, the original entire message is recovered, and its systematic payload of exactly $m=n-N=n-O_t(\log_2n)$ bits is recovered in $O_t(n^{t+1}\log_2n)$ operations. All finite decoder inputs halt. Field descriptors, greedy tables, and setup memory are constructed by actual executions, with no advice or correctness assumption in the theorem's inputs.
--
--   Differences from the source:
--   - encoding: binary strings and one-based positions → lists of Fin 2 with length predicates and current-word zero-based positions; reason: the order-preserving representation includes empty intermediate words and every unrestricted DL script
--   - encoding: the binary polynomial-basis field of order 2^b → a published finite-field Presentation with characteristic parameter 2, degree b, and its coefficient coordinates; reason: the quotient isomorphism and reconstruction certify the same field; coordinate order is constant coefficient first, and integer value is most significant bit first
--   - encoding: asymptotic deterministic bit complexity → finite programs with actual charged RAM executions and uniform positive constants before lengths and inputs; reason: the fixed instruction semantics generates costs; a function with an assigned runtime is not accepted
--   - reading: bit operations on a RAM without a prescribed tape layout → helper routines use length and packed-value natural cells, while main and generic decoders receive raw bit streams; reason: each cell read and output is charged by bit length; raw decoder streams permit bounded inspection of arbitrarily long invalid inputs
--   - generalization: the greedy setup exponent 6t+2+o(1) → the Appendix D.2 envelope Ct n^(6t+2)(log2 n)^(4t+1) in addition to every positive exponent slack; reason: the envelope is the bound the source proves in Appendix D.2 (printed p. 23) and implies n^(6t+2+o(1)); the slack clause is the headline bound itself
--   - encoding: source O_t notation for redundancy, payload length, and online time → positive constants, polylog exponents, and thresholds are quantified before n and all words; reason: no constant or program can depend on the input length or received word
--   - generalization: there are explicit codes → the statement is about the paper's own construction (encoder (5) with the Section 4 parameters, the greedy table of Section 3.3 or the bootstrapped tag code of Appendix D.2, decoded by Procedure B.2), with only the irreducible polynomial f_b left to the setup; reason: this is the construction the source's proof (Theorem 4.3, Appendix D.2) uses, and it implies the existence claim
--   - generalization: decoding and payload costs from any channel output → the same cost bounds, and halting with the Procedure B.2 output, on every finite input word; reason: the source's proof of Lemma B.3 (printed p. 17) rejects lengths outside [n-t,n+t] after reading at most n+t+1 bits, and every channel output is an instance
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Theorem 1.1, printed pp. 1–2 (PDF pp. 3–4); proof Theorem 4.3, printed p. 12 (PDF p. 14); Appendix D.2, printed p. 23 (PDF p. 25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Execution

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

/-- Theorem 1.1, including its continuation after Table 1. Every program and
constant is fixed before n. The greedy setup bound is the explicit envelope from
Appendix D.2, which implies n^(6t+2+o(1)). -/
theorem theorem_1_1 (t : ℕ) (ht : 2 ≤ t) :
    ∃ (data : ℕ → FieldData) (boot greedy : Programs)
      (C Cpayload Cred Cprefix Csetup : ℝ) (dboot ell₀ n₀ : ℕ),
      0 < C ∧ 0 < Cpayload ∧ 0 < Cred ∧ 0 < Cprefix ∧ 0 < Csetup ∧
      1 ≤ ell₀ ∧ 16 ≤ n₀ ∧
      (∀ ell : ℕ, ell₀ ≤ ell →
        (data ell).presentation.p = 2 ∧ (data ell).presentation.k = fieldWidth t ell) ∧
      (∀ n : ℕ, n₀ ≤ n →
        ell₀ ≤ tagWidth t n ∧
        (∀ v : Variant,
          1 ≤ n - suffixLength t n v ∧
          (suffixLength t n v : ℝ) ≤ Cprefix * log₂ n ∧
          FinalCorrect data v t n ∧
          redundancy n (finalCode data v t n) ≤
            (2 * t : ℕ) * log₂ n + (2 * t : ℕ) * log₂ (log₂ n) +
              Cred * (match v with
                | .bootstrapped => log₂ (log₂ (log₂ n))
                | .greedy => 1)) ∧
        ExplicitVariant data boot .bootstrapped t n C Cpayload (Csetup * (log₂ n) ^ dboot) ∧
        ExplicitVariant data greedy .greedy t n C Cpayload
          (Csetup * (n : ℝ) ^ (6 * t + 2) * (log₂ n) ^ (4 * t + 1))) ∧
      (∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n : ℕ, max N n₀ ≤ n →
        ExplicitVariant data greedy .greedy t n C Cpayload
          ((n : ℝ) ^ ((6 * t + 2 : ℕ) + epsilon))) := by sorry

end SeedRecyclingDL.Codes
