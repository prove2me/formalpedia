-- Prove2me | Theorems.Thm_StatComplexityDM_TabularPS_local_simulation_lemma
-- name    : StatComplexityDM.TabularPS.local_simulation_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:26.941595+00:00
-- url     : https://prove2.me/theorems/a9d199e4-40d9-470b-be96-dc19c0487d9d
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
--   **Formalization Note** The terminal transition term is zero. Finite alphabets replace general measurable spaces. The reward hypothesis is only the appendix's almost-sure total-reward bound; individual rewards need not lie in $[0,1]$.
-- source:
--   arXiv:2112.13487v3, Lemma F.3, (144)–(145), p. 107

import Mathlib
import Definitions.Def_StatComplexityDM_TabularPS_MDP
import Definitions.Def_StatComplexityDM_TabularPS_EpisodeTotalInUnitInterval

namespace StatComplexityDM.TabularPS

/-- Lemma F.3, equalities and inequality (144)–(145), p. 107. -/
theorem local_simulation_lemma {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W] [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (M Mbar : TabMDP S A W H) (π : Policy S A H)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1) (hM : IsTabMDP M ∧ EpisodeTotalInUnitInterval d1 rv M)
    (hMbar : IsTabMDP Mbar ∧ EpisodeTotalInUnitInterval d1 rv Mbar)
    (hπ : IsPolicy π) :
    value d1 rv M π - value d1 rv Mbar π =
      ∑ h : Fin H, ∑ s, ∑ a, occ d1 Mbar π h s a *
        ((if h.val + 1 < H then
            ∑ s', (M.P h s a s' - Mbar.P h s a s') * Vfun rv M π (h.val + 1) s'
          else 0) +
         (meanReward rv M h s a - meanReward rv Mbar h s a)) ∧
    value d1 rv M π - value d1 rv Mbar π ≤ expectedLocalTV d1 M Mbar π := by sorry

end StatComplexityDM.TabularPS
