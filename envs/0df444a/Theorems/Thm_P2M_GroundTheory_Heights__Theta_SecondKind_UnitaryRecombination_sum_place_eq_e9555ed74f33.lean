-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_sum_place_eq_e9555ed74f33
-- name    : P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_sum_place_eq_e9555ed74f33
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:44.948146+00:00
-- url     : https://prove2.me/theorems/2e745474-870f-4290-af8e-7ab5ea9c161a
-- title:
--   P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination sum place eq e9555ed74f33: P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination sum place eq e9555ed74f33
-- statement:
--   The P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination sum place eq e9555ed74f33 construction uses the P2 M Ground Theory Heights  Theta Second Kind Unitary Recombination sum place eq e9555ed74f33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L373-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/HsInnerSelfEqSumSq.lean#L373-L399

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
variable {ι : Type*} [Fintype ι]
variable (F : OrthoFrame)

theorem P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_sum_place_eq_e9555ed74f33 {τ : Fin F.f} {X : Matrix (Fin (F.p τ) ⊕ Fin (F.q τ)) (Fin (F.p τ) ⊕ Fin (F.q τ)) ℂ}
    (hX : X ∈ indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ)) :
    ∑ l : {l // F.place l = τ}, tInner (F.E l τ) X • F.E l τ = X := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SecondKind».«UnitaryRecombination».«sum_place_eq» := P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_sum_place_eq_e9555ed74f33
