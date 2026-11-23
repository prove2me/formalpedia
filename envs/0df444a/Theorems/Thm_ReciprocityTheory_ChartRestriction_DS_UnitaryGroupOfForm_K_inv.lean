-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_K_inv
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.K_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:22.974101+00:00
-- url     : https://prove2.me/theorems/afeb02ed-7acf-4f04-8bdc-2da8e404d78e
-- title:
--   Unitary Group Of Form: K inv
-- statement:
--   The Unitary Group Of Form construction uses the K inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L52-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.K_inv {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε ∧ k * kᴴ = 1 := by sorry
