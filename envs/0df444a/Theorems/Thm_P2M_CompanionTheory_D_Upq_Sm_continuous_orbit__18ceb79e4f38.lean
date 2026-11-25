-- Prove2me | Theorems.Thm_P2M_CompanionTheory_D_Upq_Sm_continuous_orbit__18ceb79e4f38
-- name    : P2M_CompanionTheory_D_Upq_Sm_continuous_orbit__18ceb79e4f38
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:29.841443+00:00
-- url     : https://prove2.me/theorems/e09f7dd1-5370-4a03-9417-ea87468e9bf7
-- title:
--   P2 M Companion Theory D Upq Sm continuous orbit  18ceb79e4f38: P2 M Companion Theory D Upq Sm continuous orbit  18ceb79e4f38
-- statement:
--   The P2 M Companion Theory D Upq Sm continuous orbit  18ceb79e4f38 construction uses the P2 M Companion Theory D Upq Sm continuous orbit  18ceb79e4f38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L158-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L158-L164

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
variable {hG : IsMatGroup G}

theorem P2M_CompanionTheory_D_Upq_Sm_continuous_orbit__18ceb79e4f38 (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {W : List (Mat n)}
    (hW : LieW G W) {X : Mat n} (hX : ∀ t, ex X t ∈ G) :
    Continuous fun p : ℝ × MG G hG => σ (ex X p.1) (dsW σ W (σ p.2.mat v)) := by sorry

alias «CompanionTheory».«D».«Upq».«Sm».«continuous_orbit₂» := P2M_CompanionTheory_D_Upq_Sm_continuous_orbit__18ceb79e4f38
