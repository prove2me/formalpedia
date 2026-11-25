-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_val_eq_zero_of_isUnit
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.val_eq_zero_of_isUnit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:26.205695+00:00
-- url     : https://prove2.me/theorems/969a8fde-6775-5b48-a9b7-f55f79b995a6
-- title:
--   Valuation Residue Lemmas: val eq zero of is Unit
-- statement:
--   The Valuation Residue Lemmas construction uses the val eq zero of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L53-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))

theorem ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.val_eq_zero_of_isUnit (x : vRing v) (hx : IsUnit x) : v (x : F) = 0 := by sorry
