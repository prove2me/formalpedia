-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_coneForm_zero_799732297cbd
-- name    : P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_coneForm_zero_799732297cbd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:21.825193+00:00
-- url     : https://prove2.me/theorems/3eb3fdbf-2c3a-4968-a8fc-8f1ae0440e27
-- title:
--   P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim cone Form zero 799732297cbd: P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim cone Form zero 799732297cbd
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim cone Form zero 799732297cbd construction uses the P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim cone Form zero 799732297cbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeProjHyperplaneDim.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeProjHyperplaneDim.lean#L20-L21

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

theorem P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_coneForm_zero_799732297cbd {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    coneForm Ψ 0 = coneFirstForm Ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeProjHyperplaneDim».«coneForm_zero» := P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_coneForm_zero_799732297cbd
