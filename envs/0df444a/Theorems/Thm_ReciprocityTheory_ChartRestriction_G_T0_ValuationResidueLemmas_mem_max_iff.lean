-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_mem_max_iff
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.mem_max_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:31.94077+00:00
-- url     : https://prove2.me/theorems/e0ca7cd8-6d59-4209-8b71-22224848e0d7
-- title:
--   Valuation Residue Lemmas: mem max iff
-- statement:
--   The Valuation Residue Lemmas construction uses the mem max iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L82-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IsUnitOfValEqZero.lean#L82-L89

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

theorem ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.mem_max_iff (x : vRing v) : x ∈ maximalIdeal (vRing v) ↔ 0 < v (x : F) := by sorry
