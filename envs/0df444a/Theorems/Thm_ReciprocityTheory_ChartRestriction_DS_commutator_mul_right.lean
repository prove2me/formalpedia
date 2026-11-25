-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_commutator_mul_right
-- name    : ReciprocityTheory.ChartRestriction.DS.commutator_mul_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:36.684909+00:00
-- url     : https://prove2.me/theorems/8ba6f6e5-df81-4991-86f5-25205f3cee91
-- title:
--   DS: commutator mul right
-- statement:
--   The DS construction uses the commutator mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Gelfand.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Gelfand.lean#L18-L20

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

theorem ReciprocityTheory.ChartRestriction.DS.commutator_mul_right (X Y Z : Module.End ℂ M) :
    X * (Y * Z) - Y * Z * X = (X * Y - Y * X) * Z + Y * (X * Z - Z * X) := by sorry
