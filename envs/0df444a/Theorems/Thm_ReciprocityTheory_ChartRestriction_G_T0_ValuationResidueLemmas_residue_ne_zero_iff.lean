-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_residue_ne_zero_iff
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.residue_ne_zero_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:50.320981+00:00
-- url     : https://prove2.me/theorems/1163f717-ef05-41df-9863-e7cc54852da2
-- title:
--   Valuation Residue Lemmas: residue ne zero iff
-- statement:
--   The Valuation Residue Lemmas construction uses the residue ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L91-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L91-L99

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

theorem ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.residue_ne_zero_iff (x : vRing v) : residue (vRing v) x ≠ 0 ↔ v (x : F) = 0 := by sorry
