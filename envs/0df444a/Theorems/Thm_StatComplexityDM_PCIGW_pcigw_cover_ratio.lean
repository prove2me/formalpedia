-- Prove2me | Theorems.Thm_StatComplexityDM_PCIGW_pcigw_cover_ratio
-- name    : StatComplexityDM.PCIGW.pcigw_cover_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:43.459984+00:00
-- url     : https://prove2.me/theorems/fe1203d2-28f5-46fa-804f-236e4efd202b
-- title:
--   Display (61) — PC-IGW occupancy cover ratio
-- statement:
--   For a tabular model $M$ and an optimal randomized policy $\pi_M$, let $\bar d_h(s,a)=\mathbb E_{\pi\sim p}[d_h^{\bar M,\pi}(s,a)]$ be the occupancy of layer $h$, state $s$, and action $a$ under Algorithm 4's normalized cover distribution. If its normalizer obeys $\lambda\le2HSA$, then
--   $$
--   d_h^{\bar M,\pi_M}(s,a)\le\bar d_h(s,a)\bigl(2HSA+\eta(f^{\bar M}(\pi_{\bar M})-f^{\bar M}(\pi_M))\bigr).
--   $$
--   This is the coverage estimate used to control the local simulation error in Proposition 5.6.
--
--   **Formalization Note** This multiplicative statement covers zero occupancies without evaluating a ratio with zero denominator. The policy cover compares against every randomized nonstationary policy.
-- source:
--   arXiv:2112.13487v3, (61), p. 37

import Mathlib
import Definitions.Def_StatComplexityDM_PCIGW_Algorithm

namespace StatComplexityDM.PCIGW

/-- Display (61), p. 37, without division by an occupancy that might vanish. -/
theorem pcigw_cover_ratio {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W]
    [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (Mbar M : StatComplexityDM.TabularPS.TabMDP S A W H)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H)
    (η lam : ℝ) (cover : Fin H → S → A → StatComplexityDM.TabularPS.Policy S A H)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1)
    (hMbar : StatComplexityDM.TabularPS.IsTabMDP Mbar ∧ RewardsNormalized d1 rv Mbar)
    (hM : StatComplexityDM.TabularPS.IsTabMDP M ∧ RewardsNormalized d1 rv M)
    (hpiStar : IsOptimalSelector d1 rv piStar)
    (hη : 0 < η) (halg : IsPCIGW d1 rv Mbar piStar η cover lam)
    (hlam : lam ≤ 2 * (H : ℝ) * Fintype.card S * Fintype.card A)
    (h : Fin H) (s : S) (a : A) :
    StatComplexityDM.TabularPS.occ d1 Mbar (piStar M) h s a ≤
      (∑ π ∈ pcigwPsi Mbar piStar cover,
        pcigwWeight d1 rv Mbar piStar η lam π * StatComplexityDM.TabularPS.occ d1 Mbar π h s a) *
      (2 * (H : ℝ) * Fintype.card S * Fintype.card A +
        η * gapBar d1 rv Mbar piStar (piStar M)) := by sorry

end StatComplexityDM.PCIGW
