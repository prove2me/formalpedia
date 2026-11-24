-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_first_index_val
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.first_index_val
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:52:20.199426+00:00
-- url     : https://prove2.me/theorems/8164ad84-6ec2-4678-99e4-85a9e62a42bb
-- title:
--   OB: first index val
-- statement:
--   The OB construction uses the first index val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/JOrbBoundB.lean#L35-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/JOrbBoundB.lean#L35-L35

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

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.first_index_val : (i0 k r').val = 0 := by sorry

attribute [defeq] ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.first_index_val
