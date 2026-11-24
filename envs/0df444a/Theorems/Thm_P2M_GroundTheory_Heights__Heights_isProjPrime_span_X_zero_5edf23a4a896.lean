-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_span_X_zero_5edf23a4a896
-- name    : P2M_GroundTheory_Heights__Heights_isProjPrime_span_X_zero_5edf23a4a896
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:37.047873+00:00
-- url     : https://prove2.me/theorems/0c3b4c88-f94d-4616-bc23-0f90484c04a6
-- title:
--   P2 M Ground Theory Heights  Heights is Proj Prime span X zero 5edf23a4a896: P2 M Ground Theory Heights  Heights is Proj Prime span X zero 5edf23a4a896
-- statement:
--   The P2 M Ground Theory Heights  Heights is Proj Prime span X zero 5edf23a4a896 construction uses the P2 M Ground Theory Heights  Heights is Proj Prime span X zero 5edf23a4a896 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsIncidenceZeroLocus.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsIncidenceZeroLocus.lean#L22-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
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
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_isProjPrime_span_X_zero_5edf23a4a896 (F : Type*) [Field F] :
    IsProjPrime (Ideal.span {(X 0 : MvPolynomial (Fin 2) F)}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isProjPrime_span_X_zero» := P2M_GroundTheory_Heights__Heights_isProjPrime_span_X_zero_5edf23a4a896
