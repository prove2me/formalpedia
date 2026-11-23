-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ballFiniteVG
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.ballFiniteVG
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:29.84981+00:00
-- url     : https://prove2.me/theorems/bf434ed4-f6b8-48b5-8c8a-de450026fe0a
-- title:
--   S7: ball Finite VG
-- statement:
--   The S7 construction uses the ball Finite VG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L83-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L83-L138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ReciprocityTheory.ChartRestriction.DS.S7.ballFiniteVG (ε : Fin n → Bool) (ν : Measure (UJ ε)) [ν.IsHaarMeasure] (R : ℝ) :
    ν {g | hs (toM g) ≤ R} < ⊤ := by sorry
