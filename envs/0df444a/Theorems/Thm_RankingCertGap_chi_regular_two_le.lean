-- Prove2me | Theorems.Thm_RankingCertGap_chi_regular_two_le
-- name    : RankingCertGap.chi_regular_two_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:55:14.772191+00:00
-- url     : https://prove2.me/theorems/8d2cedff-0ac3-455c-b99f-320e79124cbe
-- title:
--   Displays (220), (232)–(234), pp.76, 87 — the two-regular upper bound over $\mathcal A$
-- statement:
--   Let $f\in\mathcal A$, and write $\tilde\chi(f;2)$ for the infimum of the scores over nonempty two-regular instances.
--
--   1. For $m\ge1$, the long cycle is two-regular and $0\le\Phi_G(i_m,j^\star;f)-H_f(1)\le2/(m+2)!$. Hence $\tilde\chi(f;2)\le H_f(1)$.
--   2. The six-cycle $C_6$ is two-regular, and
--   $$
--   \Phi_{C_6}(i_1,j_1;f)=\int_0^1(1-y^2)f(y)\,dy+1-2\int_0^1(1-y)f(y)\,dy=1-\int_0^1(1-y)^2f(y)\,dy,
--   $$
--   $$
--   \Phi_{C_6}(i_1,j_2;f)=\Psi_{1,0}(f)=1-\int_0^1\Bigl(y-\frac{y^2}2\Bigr)f(y)\,dy.
--   $$
--   3. These constraints satisfy $\frac14H_f(1)+\frac14\Phi_{C_6}(i_1,j_1;f)+\frac12\Phi_{C_6}(i_1,j_2;f)=\frac34$, and therefore $\tilde\chi(f;2)\le3/4$.
--
--   This is the upper half of $\tilde\Gamma_{\mathcal A}(2)=3/4$.
--
--   Differences from the source:
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
--   - encoding: $f:[0,1]\to[0,1]$ → $f:\mathbb R\to\mathbb R$ with values in $[0,1]$ everywhere; reason: a printed $f$ extends (for instance by $0$), and scores read $f$ only on $[0,1]$ almost surely; same suprema and scores
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), App. I.1, p.76, eq. (220); App. M.1, eqs. (232)–(234), p.87

import Mathlib
import Definitions.Def_RankingCertGap_CertifyingCapacity
import Definitions.Def_RankingCertGap_PowerFilter
import Definitions.Def_RankingCertGap_TightInstances

namespace RankingCertGap

/-- **Displays (220), (232)–(234): the two-regular upper bound over `𝒜`.** Xu, arXiv:2610.17545 (held
file sha256 75896dd9…), App. I.1, p.76 and App. M.1, p.87. For every `f ∈ 𝒜`:
the long cycles lie in `B₂` and `0 ≤ Φ_G(i_m, j★; f) − H_f(1) ≤ 2/(m + 2)!` for `m ≥ 1`; hence
`χ̃(f; 2) ≤ H_f(1)` (eq. (220), extended to `𝒜` on p.87); `C₆` lies in `B₂` with
`Φ_{C₆}(i₁, j₁; f) = ∫₀¹ (1 − y²) f + 1 − 2∫₀¹ (1 − y) f = 1 − ∫₀¹ (1 − y)² f` (eq. (232)),
`Φ_{C₆}(i₁, j₂; f) = Ψ_{1,0}(f) = 1 − ∫₀¹ (y − y²/2) f` (eq. (233)),
`(1/4)H_f(1) + (1/4)Φ_{C₆}(i₁, j₁; f) + (1/2)Φ_{C₆}(i₁, j₂; f) = 3/4` (eq. (234)); and
`χ̃(f; 2) ≤ 3/4`.

**Formalization Note.** In `sixCycle`, `i₁ = 0`, `j₁ = 0`, `j₂ = 1`. -/
theorem chi_regular_two_le (f : ℝ → ℝ) (hf : f ∈ classA) :
    (∀ m : ℕ, 1 ≤ m →
      (longCycle m).IsRegular 2 ∧
      0 ≤ (longCycle m).Phi (longCycle.iLast m) (longCycle.jStar m) f - Hf1 f ∧
      (longCycle m).Phi (longCycle.iLast m) (longCycle.jStar m) f - Hf1 f ≤
        2 / ((m + 2).factorial : ℝ)) ∧
    chiC f (regular 2) ≤ Hf1 f ∧
    sixCycle.IsRegular 2 ∧
    sixCycle.Phi 0 0 f =
      (∫ y in (0 : ℝ)..1, (1 - y ^ 2) * f y) + 1 - 2 * ∫ y in (0 : ℝ)..1, (1 - y) * f y ∧
    (∫ y in (0 : ℝ)..1, (1 - y ^ 2) * f y) + 1 - 2 * (∫ y in (0 : ℝ)..1, (1 - y) * f y) =
      1 - ∫ y in (0 : ℝ)..1, (1 - y) ^ 2 * f y ∧
    sixCycle.Phi 0 1 f = Psi 1 0 f ∧
    Psi 1 0 f = 1 - ∫ y in (0 : ℝ)..1, (y - y ^ 2 / 2) * f y ∧
    1 / 4 * Hf1 f + 1 / 4 * sixCycle.Phi 0 0 f + 1 / 2 * sixCycle.Phi 0 1 f = 3 / 4 ∧
    chiC f (regular 2) ≤ 3 / 4 := by sorry

end RankingCertGap
