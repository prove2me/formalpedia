-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_euclid_ne_zero_de4ee5fbccea
-- name    : P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_euclid_ne_zero_de4ee5fbccea
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:06.320601+00:00
-- url     : https://prove2.me/theorems/e7a12c74-1b0c-5787-9928-22af5b655b51
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval euclid ne zero de4ee5fbccea: P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval euclid ne zero de4ee5fbccea
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval euclid ne zero de4ee5fbccea construction uses the P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval euclid ne zero de4ee5fbccea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreDegree.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreDegree.lean#L38-L48

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

theorem P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_euclid_ne_zero_de4ee5fbccea {m : ℕ} (g : MvPolynomial (Fin m) ℂ) (hg : g ≠ 0) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), eval (WithLp.ofLp w) g ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFibreDegree».«ae_eval_euclid_ne_zero» := P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_euclid_ne_zero_de4ee5fbccea
