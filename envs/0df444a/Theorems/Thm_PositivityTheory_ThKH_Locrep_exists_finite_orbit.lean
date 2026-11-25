-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Locrep_exists_finite_orbit
-- name    : PositivityTheory.ThKH.Locrep.exists_finite_orbit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:04:55.728845+00:00
-- url     : https://prove2.me/theorems/a7462a63-aec1-5e6a-b064-fdfcbae2f825
-- title:
--   Locrep: exists finite orbit
-- statement:
--   The Locrep construction uses the exists finite orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LinearIndependentOfNotMem.lean#L37-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LinearIndependentOfNotMem.lean#L37-L62

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

theorem PositivityTheory.ThKH.Locrep.exists_finite_orbit {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (K : ℕ → Subgroup G) (hanti : Antitone K) (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ n, (K n : Set G) ⊆ U)
    (f : G → V) (h1 : f 1 = 0) (hcont : ∀ l : V →ₗ[ℂ] ℂ, Continuous fun g => l (f g)) :
    ∃ n, ∃ s : Finset V, ∀ k ∈ K n, f k ∈ Submodule.span ℂ (s : Set V) := by sorry
