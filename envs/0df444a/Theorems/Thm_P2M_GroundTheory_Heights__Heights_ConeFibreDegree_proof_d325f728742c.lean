-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreDegree_proof_d325f728742c
-- name    : P2M_GroundTheory_Heights__Heights_ConeFibreDegree_proof_d325f728742c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:15.346155+00:00
-- url     : https://prove2.me/theorems/5e171ed8-999d-4462-9c19-15f642bade48
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fibre Degree proof d325f728742c: P2 M Ground Theory Heights  Heights Cone Fibre Degree proof d325f728742c
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fibre Degree proof d325f728742c construction uses the P2 M Ground Theory Heights  Heights Cone Fibre Degree proof d325f728742c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreDegree.lean#L81-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreDegree.lean#L81-L118

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjDegreeChow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreDegree
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.ConeFibreDegree

theorem P2M_GroundTheory_Heights__Heights_ConeFibreDegree_proof_d325f728742c (hD : ConeDimOfChowForm.Statement)
    (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hC : ComplexSets.DiscriminantCover.Statement) (hP : ProjDegreeChow.Statement) :
    ConeFibreDegree.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFibreDegree».«proof» := P2M_GroundTheory_Heights__Heights_ConeFibreDegree_proof_d325f728742c
