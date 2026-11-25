-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreDegree_fibreCount_eq_a532f67c3e3e
-- name    : P2M_GroundTheory_Heights__Heights_ConeFibreDegree_fibreCount_eq_a532f67c3e3e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:11.514117+00:00
-- url     : https://prove2.me/theorems/9884c562-4296-5a2b-a7fb-24805f7346ba
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fibre Degree fibre Count eq a532f67c3e3e: P2 M Ground Theory Heights  Heights Cone Fibre Degree fibre Count eq a532f67c3e3e
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fibre Degree fibre Count eq a532f67c3e3e construction uses the P2 M Ground Theory Heights  Heights Cone Fibre Degree fibre Count eq a532f67c3e3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreDegree.lean#L50-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreDegree.lean#L50-L79

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

theorem P2M_GroundTheory_Heights__Heights_ConeFibreDegree_fibreCount_eq_a532f67c3e3e {k n : ℕ} (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (π : Fin k → Fin n → ℂ) (w : EuclideanSpace ℂ (Fin k)) :
    fibreCount h W π w =
      (ComplexSets.fibre W (Matrix.of π * (h.matᵀ)⁻¹) (WithLp.ofLp w)).encard := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFibreDegree».«fibreCount_eq» := P2M_GroundTheory_Heights__Heights_ConeFibreDegree_fibreCount_eq_a532f67c3e3e
