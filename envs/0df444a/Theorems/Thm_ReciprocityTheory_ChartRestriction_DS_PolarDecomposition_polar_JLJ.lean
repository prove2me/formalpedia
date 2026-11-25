-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_JLJ
-- name    : ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_JLJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:39.646266+00:00
-- url     : https://prove2.me/theorems/51f4bc06-a5a2-4cdc-822d-cdb75b5b81a6
-- title:
--   Polar Decomposition: polar JLJ
-- statement:
--   The Polar Decomposition construction uses the polar JLJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/PolarJmConjTranspose.lean#L124-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/PolarJmConjTranspose.lean#L124-L152

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
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
open scoped Matrix.Norms.L2Operator ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.PolarDecomposition

theorem ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_JLJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Jm ε * polar_L g * Jm ε = -polar_L g := by sorry
