-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_piece_le_idealGraded_85f2dd901128
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_piece_le_idealGraded_85f2dd901128
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:59:34.170999+00:00
-- url     : https://prove2.me/theorems/e6d23641-aceb-4323-9d75-a90d0ddc074e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift piece le ideal Graded 85f2dd901128: P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift piece le ideal Graded 85f2dd901128
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift piece le ideal Graded 85f2dd901128 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift piece le ideal Graded 85f2dd901128 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L144-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L144-L152

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_piece_le_idealGraded_85f2dd901128 {J P : Ideal (Poly k N)} (hJP : J ≤ P) (Jg : FinGradedSub (S := k) (x := x) Ω)
    (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ J ∧
      f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) :
    ∀ c, Jg.piece c ≤ (idealGraded x P).piece c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThreeOnWLift».«piece_le_idealGraded» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_piece_le_idealGraded_85f2dd901128
