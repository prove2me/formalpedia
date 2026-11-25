-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeBranchLength_hyps_inhabited_4108d8e1c2e3
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ConeBranchLength_hyps_inhabited_4108d8e1c2e3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:39.732997+00:00
-- url     : https://prove2.me/theorems/88fd9325-90e1-4f96-8e2d-304bc572ab35
-- title:
--   P2 M Ground Theory Heights  Heights Targets Cone Branch Length hyps inhabited 4108d8e1c2e3: P2 M Ground Theory Heights  Heights Targets Cone Branch Length hyps inhabited 4108d8e1c2e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Cone Branch Length hyps inhabited 4108d8e1c2e3 construction uses the P2 M Ground Theory Heights  Heights Targets Cone Branch Length hyps inhabited 4108d8e1c2e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsConeBranchLength.lean#L158-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsConeBranchLength.lean#L158-L171

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsDivPushMultComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeBranchLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_hyps_inhabited_48e99e4ccda0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DegreeGeneric_hyps_inhabited_36d80aab7c4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_R1_hyps_inhabited_bed2c6b07b11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Swap_hyps_inhabited_30a7ad7515a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_DivPushMultComplex_hyps_inhabited_d7e8688bbae9

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter

theorem P2M_GroundTheory_Heights__Heights_Targets_ConeBranchLength_hyps_inhabited_4108d8e1c2e3 :
    ∃ (b : ℕ) (γ : Fin b → ConeBranch (⊥ : Ideal (MRing (PBlk 2))) (0 + Fintype.card Unit + 1) ptZeroOne)
      (ord : Fin b → ℕ),
      IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (0 + 2) ∧ IsMultiHomog (Xc 2 0) (fun _ => 1) ∧
      Xc 2 0 ∉ (⊥ : Ideal (MRing (PBlk 2))) ∧
      (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∈ divSupp ⊥ (Xc 2 0) ∧
      IsHorizontal (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∧
      (Ideal.span {X ⟨(), 0⟩} : Ideal (MRingOver ℂ (PBlk 2))) ∈
        ((Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))).map
          (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes ∧
      ConeBranchesAt ⊥ (Xc 2 0) (Ideal.span {X ⟨(), 0⟩}) ptZeroOne γ ord := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ConeBranchLength».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_Targets_ConeBranchLength_hyps_inhabited_4108d8e1c2e3
