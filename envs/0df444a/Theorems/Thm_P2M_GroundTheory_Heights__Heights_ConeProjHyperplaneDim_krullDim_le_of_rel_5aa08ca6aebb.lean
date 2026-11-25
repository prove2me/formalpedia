-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_krullDim_le_of_rel_5aa08ca6aebb
-- name    : P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_krullDim_le_of_rel_5aa08ca6aebb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:39:40.198661+00:00
-- url     : https://prove2.me/theorems/aee6aec1-a739-4ca4-a998-3d5118250354
-- title:
--   P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim krull Dim le of rel 5aa08ca6aebb: P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim krull Dim le of rel 5aa08ca6aebb
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim krull Dim le of rel 5aa08ca6aebb construction uses the P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim krull Dim le of rel 5aa08ca6aebb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeProjHyperplaneDim.lean#L68-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeProjHyperplaneDim.lean#L68-L162

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

theorem P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_krullDim_le_of_rel_5aa08ca6aebb {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Fin m → MvPolynomial (Fin n) ℂ) (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (H : Fin n → Fin m → MvPolynomial (Fin n) ℂ) (hH : ∀ i j, (H i j).totalDegree ≤ r i - 1)
    (hrel : ∀ i, X i ^ r i - ∑ j, L j * H i j ∈ I) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ((m : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeProjHyperplaneDim».«krullDim_le_of_rel» := P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_krullDim_le_of_rel_5aa08ca6aebb
