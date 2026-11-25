-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_eval_coneForm_eac9ec1d557b
-- name    : P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_eval_coneForm_eac9ec1d557b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:49.815967+00:00
-- url     : https://prove2.me/theorems/a46f5cb8-039d-4e68-a716-29d7ce6ce64c
-- title:
--   P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim eval cone Form eac9ec1d557b: P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim eval cone Form eac9ec1d557b
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim eval cone Form eac9ec1d557b construction uses the P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim eval cone Form eac9ec1d557b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeProjHyperplaneDim.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeProjHyperplaneDim.lean#L23-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeProjHyperplaneDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre mcPts psiPoly)
open GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim

theorem P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_eval_coneForm_eac9ec1d557b {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (j : Fin (e + 1)) (z : Fin n → ℂ) :
    eval z (coneForm Ψ j) = Ψ (segre fun p : Σ k, PBlk n k => z p.2) j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeProjHyperplaneDim».«eval_coneForm» := P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_eval_coneForm_eac9ec1d557b
