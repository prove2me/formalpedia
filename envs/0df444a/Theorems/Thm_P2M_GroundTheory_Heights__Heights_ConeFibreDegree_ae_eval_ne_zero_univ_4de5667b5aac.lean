-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_ne_zero_univ_4de5667b5aac
-- name    : P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_ne_zero_univ_4de5667b5aac
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:58.858354+00:00
-- url     : https://prove2.me/theorems/00a33002-bde4-4c11-bab7-335fda164082
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval ne zero univ 4de5667b5aac: P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval ne zero univ 4de5667b5aac
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval ne zero univ 4de5667b5aac construction uses the P2 M Ground Theory Heights  Heights Cone Fibre Degree ae eval ne zero univ 4de5667b5aac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreDegree.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreDegree.lean#L17-L27

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

theorem P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_ne_zero_univ_4de5667b5aac {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ u : ι → ℂ, eval u g ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFibreDegree».«ae_eval_ne_zero_univ» := P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_ne_zero_univ_4de5667b5aac
