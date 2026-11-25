-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_A_haar_exists_nilpotent_of_hypotheses
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.haar_exists_nilpotent_of_hypotheses
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:43:32.662241+00:00
-- url     : https://prove2.me/theorems/4b31a7d1-a7ea-4781-a3a5-4c3101940406
-- title:
--   A: haar exists nilpotent of hypotheses
-- statement:
--   The A construction uses the haar exists nilpotent of hypotheses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/SharpIntegralGNOfStructuralFacts.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/SharpIntegralGNOfStructuralFacts.lean#L28-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_UnitaryGroupStructuralFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_SharpIntegralGNOfStructuralFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.S0 ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.haar_exists_nilpotent_of_hypotheses (h : UnitaryGroupStructuralFacts) : HaarNExists := by sorry
