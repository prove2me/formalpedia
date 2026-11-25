-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_kill_499fcffa6e8e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_kill_499fcffa6e8e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:59:16.600234+00:00
-- url     : https://prove2.me/theorems/1b4752c8-e782-442b-a10d-e20a544c31c6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift ideal Graded kill 499fcffa6e8e: P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift ideal Graded kill 499fcffa6e8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift ideal Graded kill 499fcffa6e8e construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift ideal Graded kill 499fcffa6e8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L154-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L154-L171

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_kill_499fcffa6e8e {J : Ideal (Poly k N)} (P : Ideal (Poly k N)) (Jg : FinGradedSub (S := k) (x := x) Ω)
    (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ J ∧
      f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) :
    ∀ (f : Poly k N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ (idealGraded x P).piece a, aeval x f • z ∈ Jg.piece (a + e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThreeOnWLift».«idealGraded_kill» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_kill_499fcffa6e8e
