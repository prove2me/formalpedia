-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_Supplement_resolvents_cover
-- name    : RandomCNFDeficiency.LowerBound.Supplement.resolvents_cover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:59:58.450311+00:00
-- url     : https://prove2.me/theorems/347e3675-a108-4f6e-a5e8-692ea1099c74
-- title:
--   Lemma 4.6 — resolvents of a random formula cover all $r$-sets
-- statement:
--   Let $k=k(n)$ satisfy $\omega_n(1)\le k\le O(\log n)$, let $M=n2^k$ and $r=\frac n2-\frac n{2k}\ln\frac k{32}$ as in (33), and let $F$ consist of $M$ independent uniform signed $k$-clauses on $n$ variables. For all sufficiently large $n$,
--
--   $$\Pr\bigl[\mathrm{Resol}(F)\text{ does not cover the }\lfloor r\rfloor\text{-element variable sets}\bigr]\le 2^{-n}.$$
--
--   This is the probabilistic half of the upper bound: with overwhelming probability the low-degree consequences $\mathrm{Resol}(F)$ satisfy the covering criterion of Lemma 4.2.
--
--   Differences from the source:
--   - encoding: variables x_1, …, x_n → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - encoding: ω_n(1) ≤ k ≤ O(log n) → the published LogarithmicRegime k: k → ∞ and, for some C > 0, eventually 1 ≤ k ≤ n and k ≤ C log₂ n; reason: k ≤ C log₂ n already forces k ≤ n and divergence forces k ≥ 1 eventually; same regime
--   - encoding: F consists of M = n2^k independent uniform signed k-clauses → the published sampleProbability: uniform product mass on ordered M-tuples of published ProperClause n k, read as a clause set; reason: the same sampling law with replacement
--   - reading: the r-element variable sets, with the real r of (33) → the ⌊r⌋-element variable sets; reason: a set size must be an integer and the source does not specify rounding; changing r by less than one keeps mp = 32 + o(1) ≥ 24 in the proof, so the same failure bound holds
--   - encoding: 2^{−n} → (1/2)^n in ℝ; reason: same number
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Lemma 4.6, Equation (40), printed p. 17, PDF p. 19; Equations (33), (41), printed pp. 15, 17, PDF pp. 17, 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_UpperModel
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound

/-- Conneryd, STOC 2027 #332, Lemma 4.6, Equation (40): for the parameters (33), with
`M = n 2^k` independent uniform signed `k`-clauses, eventually the probability that `Resol(F)`
fails to cover the `⌊r⌋`-element variable sets is at most `2^{-n}`. -/
theorem resolvents_cover (k : ℕ → ℕ) (hk : LogarithmicRegime k) :
    ∀ᶠ n : ℕ in Filter.atTop,
      sampleProbability n (k n)
          (fun F => ¬ CoversSets (Resol F (k n)) ⌊upperRadius n (k n)⌋₊) ≤
        (2 : ℝ)⁻¹ ^ n := by sorry

end RandomCNFDeficiency.LowerBound.Supplement
