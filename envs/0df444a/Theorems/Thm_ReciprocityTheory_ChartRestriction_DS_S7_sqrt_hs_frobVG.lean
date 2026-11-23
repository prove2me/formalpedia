-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_sqrt_hs_frobVG
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.sqrt_hs_frobVG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:37.868155+00:00
-- url     : https://prove2.me/theorems/b28a431a-8231-40bd-9031-975c5a81b0a8
-- title:
--   S7: sqrt hs frob VG
-- statement:
--   The S7 construction uses the sqrt hs frob VG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IntegrableOfDecayVG.lean#L247-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IntegrableOfDecayVG.lean#L247-L248

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

theorem ReciprocityTheory.ChartRestriction.DS.S7.sqrt_hs_frobVG (A : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (hs A) = ‖A‖ := by sorry
