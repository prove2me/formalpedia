-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimir_tensVd
-- name    : ReciprocityTheory.ChartRestriction.DS.casimir_tensVd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:40.35927+00:00
-- url     : https://prove2.me/theorems/6700ce79-0a34-4bb3-99c5-66709c3f463f
-- title:
--   DS: casimir tens Vd
-- statement:
--   The DS construction uses the casimir tens Vd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L96-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L96-L110

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.casimir_tensVd {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) :
    casimir (tensVd E) = diagOp (casimir E) + (n : ℂ) • 1 + (2 : ℂ) • eeVd E := by sorry
