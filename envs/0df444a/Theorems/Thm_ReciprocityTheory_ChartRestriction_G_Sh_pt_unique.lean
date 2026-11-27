-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_unique
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.pt_unique
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:14:35.471637+00:00
-- url     : https://prove2.me/theorems/720072da-aa8a-4e59-ba5b-34bf85571b1e
-- title:
--   Sh: pt unique
-- statement:
--   The Sh construction uses the pt unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L36-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries
noncomputable section
variable {R : Type*} [CommRing R] {τ : Type*} {ι : Type*}
variable (T : (ι → MvPowerSeries τ R) → (ι → MvPowerSeries τ R))
  (P : (ι → MvPowerSeries τ R) → Prop)

theorem ReciprocityTheory.ChartRestriction.G.Sh.pt_unique
    (hT : ∀ k x y, P x → P y → PTAgree k x y → PTAgree (k + 1) (T x) (T y))
    {x y : ι → MvPowerSeries τ R} (hx : P x) (hy : P y) (hTx : T x = x) (hTy : T y = y) :
    x = y := by sorry
