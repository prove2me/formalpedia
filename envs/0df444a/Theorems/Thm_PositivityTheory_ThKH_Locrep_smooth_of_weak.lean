-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Locrep_smooth_of_weak
-- name    : PositivityTheory.ThKH.Locrep.smooth_of_weak
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:24.183645+00:00
-- url     : https://prove2.me/theorems/99cb72f3-7034-479b-9d8f-7c2aef66aebb
-- title:
--   Locrep: smooth of weak
-- statement:
--   The Locrep construction uses the smooth of weak property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LinearIndependentOfNotMem.lean#L64-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LinearIndependentOfNotMem.lean#L64-L130

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsSideBis
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LinearIndependentOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology

theorem PositivityTheory.ThKH.Locrep.smooth_of_weak {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V)
    (K : ℕ → Subgroup G) (hanti : Antitone K) (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ n, (K n : Set G) ⊆ U)
    (ω : G → Module.End ℂ V) (hpres : ∀ g ∈ K 0, ∀ φ ∈ W, ω g φ ∈ W) (hone : ∀ φ ∈ W, ω 1 φ = φ)
    (hmul : ∀ g ∈ K 0, ∀ g' ∈ K 0, ∀ φ ∈ W, ω (g * g') φ = ω g (ω g' φ))
    (hcont : ∀ l : V →ₗ[ℂ] ℂ, ∀ φ ∈ W, Continuous fun g => l (ω g φ)) :
    ∀ φ ∈ W, ∃ n, ∀ k ∈ K n, ω k φ = φ := by sorry
