-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_cone_rel_fa3848bfc4a0
-- name    : P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_cone_rel_fa3848bfc4a0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:30.924078+00:00
-- url     : https://prove2.me/theorems/151340aa-7073-4931-954a-af08f62cfe3f
-- title:
--   P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim cone rel fa3848bfc4a0: P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim cone rel fa3848bfc4a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim cone rel fa3848bfc4a0 construction uses the P2 M Ground Theory Heights  Heights Cone Proj Hyperplane Dim cone rel fa3848bfc4a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeProjHyperplaneDim.lean#L34-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeProjHyperplaneDim.lean#L34-L66

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

theorem P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_cone_rel_fa3848bfc4a0 {n e : ℕ} {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hP : IsArithVar P (e + 1))
    (hΨ : IsGoodProj P Ψ) (i : Fin n) :
    ∃ r : ℕ, 0 < r ∧ ∃ H : Fin (e + 1) → MvPolynomial (Fin n) ℂ,
      (∀ j, (H j).totalDegree ≤ r - 1) ∧
      X i ^ r - ∑ j, coneForm Ψ j * H j ∈ (complexFibreIdeal P).radical := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeProjHyperplaneDim».«cone_rel» := P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_cone_rel_fa3848bfc4a0
