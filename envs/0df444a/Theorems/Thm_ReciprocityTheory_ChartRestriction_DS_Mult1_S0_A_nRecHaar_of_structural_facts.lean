-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_A_nRecHaar_of_structural_facts
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.nRecHaar_of_structural_facts
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:25.135241+00:00
-- url     : https://prove2.me/theorems/8330cac1-6310-42f6-8c5f-ff8f9b1c56b1
-- title:
--   A: n Rec Haar of structural facts
-- statement:
--   The A construction uses the n Rec Haar of structural facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/SharpIntegralGNOfStructuralFacts.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/SharpIntegralGNOfStructuralFacts.lean#L12-L13

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

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.nRecHaar_of_structural_facts (h : UnitaryGroupStructuralFacts) : NRecHaar := by sorry
