-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_theorem_h_1
-- name    : PrefixMixLearn.Proper.theorem_h_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:46:13.274398+00:00
-- url     : https://prove2.me/theorems/17996177-1539-4a84-af2c-5164d09bdd8b
-- title:
--   Theorem H.1 — supplied-scale proper candidate generation: if OPT^(2)_α(P) ≤ ζ the list covers P within κ^{-20}ζ w.p. 1 − δ
-- statement:
--   There is one fair-coin program with prefix-conditional access such that for every known rational $\alpha\in(0,1/2)$ there is an exponent $c$ with the following property. For every $T\ge1$, rational $0<\zeta\le1$, $0<\delta<1$ and full-support $P$ on $\{0,1\}^T$, given $(T,\alpha,\zeta,\delta)$ the program returns on every run a nonempty list of proper balanced dyadic two-product mixtures $\hat M_r$, with log-cost (hence bit time, oracle calls, returned symbols, learner bits and output length, so also the list size) at most $(T+\lceil1/\zeta\rceil+\lceil\log(1/\delta)\rceil+\text{input length}+2)^c$; and if $\eta=\min_{M\in\mathcal M_{2,\alpha,T}}d_{TV}(P,M)\le\zeta$ then with probability at least $1-\delta$
--   $$\min_r d_{TV}(P,\hat M_r)\le C_{gen}\,\zeta,\qquad C_{gen}=\kappa(\alpha)^{-20}.$$
--   This is the candidate generator; Theorem 3.1 runs it over a geometric grid of scales and selects with Theorem B.4.
--
--   Differences from the source:
--   - reading: a finite algorithm … its resources are polynomial in T, ζ⁻¹, log(1/δ) and input lengths (α a fixed known rational) → one program taking α as input; for each α an exponent c with log-cost ≤ (T + ⌈1/ζ⌉ + ⌈log(1/δ)⌉ + encLen input + 2)^c on every run; reason: α is fixed in Appendix H, so the polynomial may depend on α; the uniform dependence is Corollary H.4 / Theorem 3.1
--   - encoding: a nonempty polynomial-size list of proper balanced dyadic mixture candidates → output = concatenated encodings of a nonempty list of proper mixture codes; reason: Appendix B.1 representation; list size ≤ output length ≤ log-cost
--   - encoding: "a prefix-conditional algorithm" (no machine is named; costs include bit operations, query writing, response processing, random bits, output length, input reading; learner randomness is fair bits) → a program of the fair-coin log-cost RAM `Machine` (instructions charged by bit lengths; `coin` draws one fair bit; `query` sends a 0/1 prefix to `condOracle P` and is charged for every cell read and written; `halt` for every output cell); a run's law is over the coins and the oracle replies; reason: the paper's model made explicit; one log-cost bound bounds every listed resource (calls, written and returned symbols, coins, bit time, output length)
--   - encoding: COND_P accepts prefixes with 0 ≤ |h| < T (Definition 2.1) → `condOracle P` answers a 0/1 list h with |h| < T (and positive mass) by a fresh suffix with law P_h; every other query gets the empty reply; reason: the paper never issues such queries; the empty reply carries no information about P
--   - encoding: coordinates i = 1, …, T; laws on {0,1}^T → `Fin T`, coordinate i ↦ i.val + 1; laws are real functions on `Fin T → Bool` with `IsLaw`; reason: Lean convention; same statement
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 58 (PDF 60), Theorem H.1, (H.2)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws
import Definitions.Def_PrefixMixLearn_Proper_Ledger
import Definitions.Def_PrefixMixLearn_Proper_Machine

namespace PrefixMixLearn.Proper

/-- Theorem H.1 (supplied-scale proper candidate generation): one fair-coin program with
prefix-conditional access which, given `T`, the known rational `α ∈ (0, 1/2)`, rational
`0 < ζ ≤ 1` and `0 < δ < 1`, for every full-support `P` returns on every run a nonempty list of
proper balanced dyadic two-product mixtures, with log-cost (hence bit time, calls, returned symbols,
coins and output length) polynomial in `T, ζ⁻¹, log(1/δ)` and the input length for each fixed `α`;
and if `η = min_{M ∈ M_{2,α,T}} d_TV(P, M) ≤ ζ`, then with probability at least `1 − δ` some entry
has `d_TV(P, M̂_r) ≤ C_gen ζ` (H.2), `C_gen = κ^{-20}`. -/
theorem theorem_h_1 :
    ∃ prog : Program, ∀ α : ℚ, 0 < α → α < 1 / 2 → ∃ c : ℕ,
      ∀ (T : ℕ), 1 ≤ T → ∀ (ζ δ : ℚ), 0 < ζ → ζ ≤ 1 → 0 < δ → δ < 1 →
      ∀ (P : Cube T → ℝ), IsLaw P → FullSupport P →
        HaltsWithin prog (condOracle P) (generatorInput T α ζ δ)
          (((T + ⌈1 / ζ⌉₊ + ⌈Real.log (1 / (δ : ℝ))⌉₊ +
            encLen (generatorInput T α ζ δ) + 2 : ℕ) : ℝ) ^ c) ∧
        OutputsSatisfy prog (condOracle P) (generatorInput T α ζ δ)
          (fun o => ∃ L : List (MixCode T), L ≠ [] ∧ o = encMixList L ∧
            ∀ c ∈ L, IsProperMixCode α c) ∧
        (OPT2 α P ≤ ζ →
          1 - (δ : ℝ) ≤ outProb prog (condOracle P) (generatorInput T α ζ δ)
            (fun o => ∃ L : List (MixCode T), o = encMixList L ∧
              ∃ c ∈ L, tv P (mixOfCode c) ≤ Cgen α * ζ)) := by sorry

end PrefixMixLearn.Proper
