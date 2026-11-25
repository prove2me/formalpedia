-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbIrrelevantZero_hypotheses_example_2156e605e0ff
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbIrrelevantZero_hypotheses_example_2156e605e0ff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:51:44.442373+00:00
-- url     : https://prove2.me/theorems/5e4d20ce-cdf6-5464-b779-be068789e127
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Irrelevant Zero hypotheses example 2156e605e0ff: P2 M Ground Theory Heights  Heights Field Numbers Hilb Irrelevant Zero hypotheses example 2156e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Irrelevant Zero hypotheses example 2156e605e0ff construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Irrelevant Zero hypotheses example 2156e605e0ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegreeBound.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegreeBound.lean#L42-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_hypotheses_example_4051c0ae0704
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hypotheses_example_aa81192740bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_hypotheses_example_0ca615a70965
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_hypotheses_example_499b36c3f9ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumBaseChange_hypotheses_example_41a071ddf012
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumBase_hypotheses_example_77f0c5696e4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumZeroSlot_hypotheses_example_79ecb2ebf4ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_hypotheses_example_652314d4875e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_hypotheses_example_ad7ad2c3722d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProductWithProjectiveSpace_hypotheses_example_bd159c78b846
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaContracted_hypotheses_example_9fbe5bc3ae39
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_hypotheses_example_2d68edfc775d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbIrrelevantZero_hypotheses_example_2156e605e0ff :
    ¬ IsRelevant (Ideal.span (Set.range X) : Ideal (MRing (ProjIdx 1) ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbIrrelevantZero».«hypotheses_example» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbIrrelevantZero_hypotheses_example_2156e605e0ff
