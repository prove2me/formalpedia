-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_Supplement_theorem_4_3
-- name    : SeedRecyclingDL.Codes.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:42:17.327195+00:00
-- url     : https://prove2.me/theorems/a429d73c-d57a-423d-95ca-7e73aac6eb59
-- title:
--   Theorem 4.3 — Damerau–Levenshtein codes for every fixed t ≥ 1
-- statement:
--   Fix an integer $t\ge1$. A Damerau–Levenshtein (DL) operation on a binary word is an insertion, a deletion, a substitution, or an adjacent transposition, and a code $C\subseteq\{0,1\}^n$ corrects $t$ DL errors if the radius-$t$ DL balls of distinct codewords are disjoint. Then there are uniform deterministic setup, encoding, full-message decoding and payload-decoding programs for two binary code families such that, for all sufficiently large $n$, each encoder is injective into $\{0,1\}^n$, its image $C_n$ corrects any combination of at most $t$ DL errors, and
--
--   $$\begin{aligned}
--   \text{(a) bootstrapped: }\; n-\log_2|C_n| &\le 2t\log_2 n+2t\log_2\log_2 n+O_t(\log_2\log_2\log_2 n),\\
--   \text{(b) greedy: }\; n-\log_2|C_n| &\le 2t\log_2 n+2t\log_2\log_2 n+O_t(1).
--   \end{aligned}$$
--
--   The bootstrapped precomputation takes $\mathrm{polylog}(n)$ time; the greedy precomputation takes $n^{6t+2+o(1)}$ time, including the explicit Appendix D.2 envelope $C_t\,n^{6t+2}(\log_2 n)^{4t+1}$. In both variants encoding and full-message decoding take $O_t(n^{2t+2}\log_2^2 n)$ bit operations, and the payload, the first $n-O_t(\log_2 n)$ bits of the codeword, is recovered from any channel output in $O_t(n^{t+1}\log_2 n)$ bit operations.
--
--   This is the paper's Damerau–Levenshtein result at its full domain $t\ge1$. The mission's goal, Theorem 1.1, is the same statement for $t\ge2$; the case $t=1$ (one error of any of the four kinds) is covered only here.
--
--   **Formalization Note** The statement reuses, unchanged, every object of the base mission (`FinalCorrect`, `finalCode`, `ExplicitVariant`, `suffixLength`, `redundancy`) and differs from the published goal `SeedRecyclingDL.Codes.theorem_1_1` only in the hypothesis $1\le t$ in place of $2\le t$. Programs and constants are chosen after $t$ and before $n$; the threshold $n_0\ge16$ makes all three iterated logarithms positive. Logarithms are base 2.
--
--   Differences from the source:
--   - encoding: binary strings and one-based positions → lists of Fin 2 with length predicates and current-word zero-based positions; reason: the order-preserving representation includes empty intermediate words and every unrestricted DL script
--   - encoding: the binary polynomial-basis field of order 2^b → a published finite-field Presentation with characteristic parameter 2, degree b, and its coefficient coordinates; reason: the quotient isomorphism and reconstruction certify the same field; coordinate order is constant coefficient first, and integer value is most significant bit first
--   - encoding: asymptotic deterministic bit complexity → finite programs with actual charged RAM executions and uniform positive constants before lengths and inputs; reason: the fixed instruction semantics generates costs; a function with an assigned runtime is not accepted
--   - reading: bit operations on a RAM without a prescribed tape layout → helper routines use length and packed-value natural cells, while main and generic decoders receive raw bit streams; reason: each cell read and output is charged by bit length; raw decoder streams permit bounded inspection of arbitrarily long invalid inputs
--   - generalization: the greedy precomputation time n^(6t+2+o(1)) → the Appendix D.2 envelope Ct n^(6t+2)(log2 n)^(4t+1) in addition to every positive exponent slack; reason: the envelope is the bound the source proves in Appendix D.2 (printed p. 23) and implies n^(6t+2+o(1)); the slack clause is the stated bound itself
--   - encoding: source O_t notation for redundancy, payload length, polylog precomputation and online time → positive constants, polylog exponents, and thresholds quantified after t and before n and all words; reason: no constant or program can depend on the input length or received word
--   - generalization: there are explicit codes → the statement is about the paper's own construction (encoder (5) with the Section 4 parameters, the greedy table of Section 3.3 or the bootstrapped tag code of Appendix D.2, decoded by Procedure B.2), with only the irreducible polynomial f_b left to the setup; reason: this is the construction the source's proof (Theorem 4.3, Appendix D.2) uses, and it implies the existence claim
--   - generalization: encoding/decoding and payload-recovery costs for channel outputs → the same cost bounds, and halting with the Procedure B.2 output, on every finite input word; reason: the source's proof of Lemma B.3 (printed p. 17) rejects lengths outside [n-t,n+t] after reading at most n+t+1 bits, and every channel output is an instance
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Theorem 4.3, printed p. 12 (PDF p. 14); proof printed p. 12 (PDF p. 14), Theorem C.7 printed p. 20 (PDF p. 22), Appendix D.2 printed p. 23 (PDF p. 25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Execution

set_option autoImplicit false

namespace SeedRecyclingDL.Codes.Supplement

/-- Bui–Hagiwara–Wang–Vu, STOC 2027 submission #1449, Theorem 4.3, printed
p. 12 (PDF p. 14), for every fixed t ≥ 1. Clause for clause the published
`SeedRecyclingDL.Codes.theorem_1_1` with `1 ≤ t` in place of `2 ≤ t`. Every
program and constant is chosen after t and before n. The greedy setup bound is
the explicit envelope of Appendix D.2, which implies n^(6t+2+o(1)); the per-ε
clause states the n^(6t+2+o(1)) form directly. -/
theorem theorem_4_3 (t : ℕ) (ht : 1 ≤ t) :
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

end SeedRecyclingDL.Codes.Supplement
