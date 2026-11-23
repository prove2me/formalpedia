-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gelfand_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.gelfand_comm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:54.925887+00:00
-- url     : https://prove2.me/theorems/65b853f9-acc2-4649-815e-98ba8228b75e
-- title:
--   DS: gelfand comm
-- statement:
--   The DS construction uses the gelfand comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Gelfand.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Gelfand.lean#L41-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_Lemmata_MiscLemmasP_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
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

theorem ReciprocityTheory.ChartRestriction.DS.gelfand_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (k : ℕ) (a b : Fin n) :
    E a b * gelfand E k = gelfand E k * E a b := by sorry
