-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_matrix_decomp_lieAlgebra
-- name    : ReciprocityTheory.ChartRestriction.DS.matrix_decomp_lieAlgebra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:52.602367+00:00
-- url     : https://prove2.me/theorems/94eb3fc3-a621-4e6e-9bad-136b651d48a9
-- title:
--   DS: matrix decomp lie Algebra
-- statement:
--   The DS construction uses the matrix decomp lie Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L71-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOneA
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
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.matrix_decomp_lieAlgebra (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    M = (1 / 2 : ℂ) • (M - Jm ε * Mᴴ * Jm ε) + Complex.I • ((-Complex.I / 2 : ℂ) • (M + Jm ε * Mᴴ * Jm ε)) := by sorry
