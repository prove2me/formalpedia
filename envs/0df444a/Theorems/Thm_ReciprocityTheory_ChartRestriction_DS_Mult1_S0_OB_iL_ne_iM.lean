-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_iL_ne_iM
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.iL_ne_iM
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:00:33.460974+00:00
-- url     : https://prove2.me/theorems/842f7ec0-76f1-46bf-8c90-91aa3b3ff9d1
-- title:
--   OB: i L ne i M
-- statement:
--   The OB construction uses the i L ne i M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/JOrbBoundB.lean#L44-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/JOrbBoundB.lean#L44-L44

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_JOrbBoundB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.S0 ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.iL_ne_iM (j : Fin (2 * r' + k + 1)) : iL k r' ≠ iM k r' j := by sorry
