-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_matrix_ne_zero_3da30494ff5f
-- name    : P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_matrix_ne_zero_3da30494ff5f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:58.516342+00:00
-- url     : https://prove2.me/theorems/0d092c05-7cfc-562c-b959-e4bfd5b8661c
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval matrix ne zero 3da30494ff5f: P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval matrix ne zero 3da30494ff5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval matrix ne zero 3da30494ff5f construction uses the P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval matrix ne zero 3da30494ff5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreDegree.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreDegree.lean#L29-L36

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

theorem P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_matrix_ne_zero_3da30494ff5f {k n : ℕ} (g : MvPolynomial (Fin k × Fin n) ℂ) (hg : g ≠ 0) :
    ∀ᵐ π : Fin k → Fin n → ℂ, eval (fun ij => π ij.1 ij.2) g ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFibreDegree».«ae_eval_matrix_ne_zero» := P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_matrix_ne_zero_3da30494ff5f
