-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_OB_first_ne_middle_index
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.first_ne_middle_index
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:00:19.358818+00:00
-- url     : https://prove2.me/theorems/92cad91f-008a-4571-8455-d64db2f9752d
-- title:
--   OB: first ne middle index
-- statement:
--   The OB construction uses the first ne middle index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/JOrbBoundB.lean#L41-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/JOrbBoundB.lean#L41-L41

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

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB.first_ne_middle_index (j : Fin (2 * r' + k + 1)) : i0 k r' ≠ iM k r' j := by sorry
