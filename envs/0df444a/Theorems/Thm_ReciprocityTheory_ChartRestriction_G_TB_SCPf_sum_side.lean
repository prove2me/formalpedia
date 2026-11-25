-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_sum_side
-- name    : ReciprocityTheory.ChartRestriction.G.TB.SCPf.sum_side
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:18.338808+00:00
-- url     : https://prove2.me/theorems/331bc8c9-0ba3-482e-b21e-13c6a626b9e7
-- title:
--   SCPf: sum side
-- statement:
--   The SCPf construction uses the sum side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondOrderIterateEqZero.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondOrderIterateEqZero.lean#L13-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.TB.SCPf.sum_side {M : Type} [AddCommMonoid M] (s : ι → Bool) (g : ι → ι → M)
    (hg : ∀ l l', g l l' ≠ 0 → s l = true ∧ s l' = false) :
    ∑ l, ∑ l', g l l' = ∑ i, ∑ j, g ((sideE s).symm (Sum.inl i)) ((sideE s).symm (Sum.inr j)) := by sorry
