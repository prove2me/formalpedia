-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurePreserving_curry_matrix_e2df5b44d13a
-- name    : P2M_GroundTheory_Heights__Heights_measurePreserving_curry_matrix_e2df5b44d13a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:43.956897+00:00
-- url     : https://prove2.me/theorems/1994a294-b607-4a29-8046-47f9baf114b9
-- title:
--   P2 M Ground Theory Heights  Heights measure Preserving curry matrix e2df5b44d13a: P2 M Ground Theory Heights  Heights measure Preserving curry matrix e2df5b44d13a
-- statement:
--   The P2 M Ground Theory Heights  Heights measure Preserving curry matrix e2df5b44d13a construction uses the P2 M Ground Theory Heights  Heights measure Preserving curry matrix e2df5b44d13a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L160-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L160-L174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_measurePreserving_curry_matrix_e2df5b44d13a (m n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin m) (Fin n) ℂ)
      (volume : Measure (Fin m × Fin n → ℂ)) (Measure.pi fun _ : Fin m => (volume : Measure (Fin n → ℂ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«measurePreserving_curry_matrix» := P2M_GroundTheory_Heights__Heights_measurePreserving_curry_matrix_e2df5b44d13a
