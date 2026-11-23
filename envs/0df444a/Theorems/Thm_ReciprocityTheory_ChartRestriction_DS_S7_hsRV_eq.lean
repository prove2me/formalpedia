-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hsRV_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.hsRV_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:15.154766+00:00
-- url     : https://prove2.me/theorems/84e4fa38-8836-46b1-89c7-fa64ae3d441f
-- title:
--   S7: hs RV eq
-- statement:
--   The S7 construction uses the hs RV eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L283-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L283-L286

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
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

theorem ReciprocityTheory.ChartRestriction.DS.S7.hsRV_eq {Q : Type} [Fintype Q] (A : Matrix (Fin n) Q ℂ) : hsRV A = ‖A‖ ^ 2 := by sorry
