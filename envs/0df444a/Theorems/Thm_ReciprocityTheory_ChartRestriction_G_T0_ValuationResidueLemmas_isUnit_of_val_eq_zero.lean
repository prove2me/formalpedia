-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_isUnit_of_val_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.isUnit_of_val_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:05.32308+00:00
-- url     : https://prove2.me/theorems/74afcb16-f7c6-4679-a676-22e8a52b1625
-- title:
--   Valuation Residue Lemmas: is Unit of val eq zero
-- statement:
--   The Valuation Residue Lemmas construction uses the is Unit of val eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L63-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L63-L80

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

theorem ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.isUnit_of_val_eq_zero (x : vRing v) (hx : v (x : F) = 0) : IsUnit x := by sorry
