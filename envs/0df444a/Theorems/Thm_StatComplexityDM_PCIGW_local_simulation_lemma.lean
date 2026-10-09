-- Prove2me | Theorems.Thm_StatComplexityDM_PCIGW_local_simulation_lemma
-- name    : StatComplexityDM.PCIGW.local_simulation_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:44.671026+00:00
-- url     : https://prove2.me/theorems/aead3c54-e227-4752-bf25-00ce102ed072
-- title:
--   Lemma F.3 (144)–(145) — local simulation bound for tabular MDPs
-- statement:
--   Let $M,\bar M$ be tabular MDPs whose total reward lies in $[0,1]$ almost surely, sharing an initial law, and let $\pi$ be a randomized nonstationary policy. The value difference equals the sum, under the occupancy law of $(\bar M,\pi)$, of the transition-kernel difference applied to the continuation value $V^{M,\pi}_{h+1}$ and the difference in mean rewards. It is bounded by
--   $$
--   f^M(\pi)-f^{\bar M}(\pi)\le
--   \sum_{h=1}^{H}\mathbb E^{\bar M,\pi}\!\left[
--     D_{TV}(P_h^M(\cdot\mid s_h,a_h),P_h^{\bar M}(\cdot\mid s_h,a_h))
--     +D_{TV}(R_h^M(\cdot\mid s_h,a_h),R_h^{\bar M}(\cdot\mid s_h,a_h))\right].
--   $$
--   This relates value error to discrepancies at the states and actions visited by the reference model.
--
--   **Formalization Note** The terminal transition term is zero. Finite alphabets replace general measurable spaces. Both models satisfy only the paper's hypothesis that total reward lies in $[0,1]$ almost surely; no per-step sign condition is assumed.
-- source:
--   arXiv:2112.13487v3, Lemma F.3, (144)–(145), p. 107

import Mathlib
import Definitions.Def_StatComplexityDM_PCIGW_MDP

namespace StatComplexityDM.PCIGW

/-- Lemma F.3, equalities and inequality (144)–(145), p. 107. -/
theorem local_simulation_lemma {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W] [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (M Mbar : StatComplexityDM.TabularPS.TabMDP S A W H) (π : StatComplexityDM.TabularPS.Policy S A H)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1) (hM : StatComplexityDM.TabularPS.IsTabMDP M ∧ RewardsNormalized d1 rv M)
    (hMbar : StatComplexityDM.TabularPS.IsTabMDP Mbar ∧ RewardsNormalized d1 rv Mbar)
    (hπ : StatComplexityDM.TabularPS.IsPolicy π) :
    StatComplexityDM.TabularPS.value d1 rv M π - StatComplexityDM.TabularPS.value d1 rv Mbar π =
      ∑ h : Fin H, ∑ s, ∑ a, StatComplexityDM.TabularPS.occ d1 Mbar π h s a *
        ((if h.val + 1 < H then
            ∑ s', (M.P h s a s' - Mbar.P h s a s') * StatComplexityDM.TabularPS.Vfun rv M π (h.val + 1) s'
          else 0) +
         (StatComplexityDM.TabularPS.meanReward rv M h s a - StatComplexityDM.TabularPS.meanReward rv Mbar h s a)) ∧
    StatComplexityDM.TabularPS.value d1 rv M π - StatComplexityDM.TabularPS.value d1 rv Mbar π ≤ StatComplexityDM.TabularPS.expectedLocalTV d1 M Mbar π := by sorry

end StatComplexityDM.PCIGW
