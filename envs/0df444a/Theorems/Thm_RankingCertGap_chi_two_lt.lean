-- Prove2me | Theorems.Thm_RankingCertGap_chi_two_lt
-- name    : RankingCertGap.chi_two_lt
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:55:16.680116+00:00
-- url     : https://prove2.me/theorems/4716fbbb-b44c-4036-88cf-92d101e88ada
-- title:
--   Display (231) and the rational bound, pp.86–87
-- statement:
--   For every $f\in\mathcal A$, $\chi(f;2)$ is at most each of $H_f(1)$, $\Psi_{0,0}(f)$, $\Psi_{1,1}(f)$ and $\Psi_{2,1}(f)$, and their convex combination with weights $194/1000$, $512/1000$, $63/1000$, $231/1000$ gives
--
--   $$
--   \chi(f;2)\le\frac{2853}{4000}+\int_0^1k(y)f(y)\,dy\le\frac{2853}{4000}+\int_0^1(k(y))_+\,dy.
--   $$
--
--   Independently of $f$,
--
--   $$
--   \frac{2853}{4000}+\int_0^1(k(y))_+\,dy\le\frac{2853}{4000}+J\Bigl(\frac{746005}{10^6}\Bigr)-J\Bigl(\frac{229499}{10^6}\Bigr)+J(1)-J\Bigl(\frac{824213}{10^6}\Bigr)+\frac{6117}{2000\cdot10^{12}}<\frac{715361}{10^6}.
--   $$
--
--   Since the final bound does not depend on $f$, this gives the strict inequality $\Gamma_{\mathcal A}(2)<715361/10^6$.
--
--   Differences from the source:
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
--   - encoding: $f:[0,1]\to[0,1]$ → $f:\mathbb R\to\mathbb R$ with values in $[0,1]$ everywhere; reason: a printed $f$ extends (for instance by $0$), and scores read $f$ only on $[0,1]$ almost surely; same suprema and scores
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), App. M.1, eq. (231), p.86; p.87

import Mathlib
import Definitions.Def_RankingCertGap_CertifyingCapacity
import Definitions.Def_RankingCertGap_PowerFilter

namespace RankingCertGap

/-- **Display (231) and the rational bound.** Xu, arXiv:2610.17545 (held file sha256 75896dd9…), App.
M.1, pp.86–87. For every `f ∈ 𝒜`, `χ(f; 2)` is at most each of `H_f(1)`, `Ψ_{0,0}(f)`, `Ψ_{1,1}(f)`,
`Ψ_{2,1}(f)`, and `χ(f; 2) ≤ 2853/4000 + ∫₀¹ k f ≤ 2853/4000 + ∫₀¹ k₊` (eq. (231)). Independently of
`f`, `2853/4000 + ∫₀¹ k₊ ≤ 2853/4000 + J(746005/10⁶) − J(229499/10⁶) + J(1) − J(824213/10⁶)
+ 6117/(2000 · 10¹²) < 715361/10⁶`.

**Formalization Note.** The positive part is `max (k y) 0`. The last two conjuncts are the part that
gives the strict first clause of the goal, since a supremum of values below a bound gives only `≤`. -/
theorem chi_two_lt :
    (∀ f ∈ classA,
      chiC f (onDegLE 2) ≤ Hf1 f ∧
      chiC f (onDegLE 2) ≤ Psi 0 0 f ∧
      chiC f (onDegLE 2) ≤ Psi 1 1 f ∧
      chiC f (onDegLE 2) ≤ Psi 2 1 f ∧
      chiC f (onDegLE 2) ≤ 2853 / 4000 + ∫ y in (0 : ℝ)..1, kernelK y * f y ∧
      (2853 / 4000 + ∫ y in (0 : ℝ)..1, kernelK y * f y) ≤
        2853 / 4000 + ∫ y in (0 : ℝ)..1, max (kernelK y) 0) ∧
    (2853 / 4000 + ∫ y in (0 : ℝ)..1, max (kernelK y) 0) ≤
      2853 / 4000 + kernelJ (746005 / 10 ^ 6) - kernelJ (229499 / 10 ^ 6) + kernelJ 1 -
        kernelJ (824213 / 10 ^ 6) + 6117 / (2000 * 10 ^ 12) ∧
    2853 / 4000 + kernelJ (746005 / 10 ^ 6) - kernelJ (229499 / 10 ^ 6) + kernelJ 1 -
        kernelJ (824213 / 10 ^ 6) + 6117 / (2000 * 10 ^ 12) < (715361 : ℝ) / 10 ^ 6 := by sorry

end RankingCertGap
