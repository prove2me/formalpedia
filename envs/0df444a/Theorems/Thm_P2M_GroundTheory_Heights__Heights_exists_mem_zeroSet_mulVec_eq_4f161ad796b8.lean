-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_mem_zeroSet_mulVec_eq_4f161ad796b8
-- name    : P2M_GroundTheory_Heights__Heights_exists_mem_zeroSet_mulVec_eq_4f161ad796b8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:17.7078+00:00
-- url     : https://prove2.me/theorems/902a9212-63bb-4efe-846e-f9efc491ece2
-- title:
--   P2 M Ground Theory Heights  Heights exists mem zero Set mul Vec eq 4f161ad796b8: P2 M Ground Theory Heights  Heights exists mem zero Set mul Vec eq 4f161ad796b8
-- statement:
--   The P2 M Ground Theory Heights  Heights exists mem zero Set mul Vec eq 4f161ad796b8 construction uses the P2 M Ground Theory Heights  Heights exists mem zero Set mul Vec eq 4f161ad796b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFiniteFibreDim.lean#L23-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFiniteFibreDim.lean#L23-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFiniteFibreDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
open scoped Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_exists_mem_zeroSet_mulVec_eq_4f161ad796b8 {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {B : Matrix (Fin d) (Fin n) ℂ} (hB : ComplexSets.IsFiniteProjection J B) (x : Fin d → ℂ) :
    ∃ z ∈ ComplexSets.zeroSet J, B *ᵥ z = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_mem_zeroSet_mulVec_eq» := P2M_GroundTheory_Heights__Heights_exists_mem_zeroSet_mulVec_eq_4f161ad796b8
