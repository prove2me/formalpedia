-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_lift_of_subsingleton_684c811e2477
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_lift_of_subsingleton_684c811e2477
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:00:58.773894+00:00
-- url     : https://prove2.me/theorems/96beb239-77b4-5265-976c-b35d63c28a5f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift lift of subsingleton 684c811e2477: P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift lift of subsingleton 684c811e2477
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift lift of subsingleton 684c811e2477 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three On WLift lift of subsingleton 684c811e2477 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L179-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWLift.lean#L179-L269

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_lift_of_subsingleton_684c811e2477 (Qc K : SubSystem S x Ω) (hKQ : ∀ I, K.sub I ≤ Qc.sub I)
    (hsub : Subsingleton (K.H 1)) (s : Chart x → Ω) (hs : ∀ I, s I ∈ Qc.sub I)
    (hcompat : ∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ K.sub I₂) :
    ∃ t ∈ Qc.secs, ∀ I, t - s I ∈ K.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThreeOnWLift».«lift_of_subsingleton» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_lift_of_subsingleton_684c811e2477
