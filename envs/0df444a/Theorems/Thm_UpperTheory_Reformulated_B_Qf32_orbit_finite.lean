-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qf32_orbit_finite
-- name    : UpperTheory.Reformulated.B.Qf32.orbit_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:58.367953+00:00
-- url     : https://prove2.me/theorems/c82763f5-64a0-4921-bda8-f7594acc1936
-- title:
--   Qf32: orbit finite
-- statement:
--   The Qf32 construction uses the orbit finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/OrbitFinite.lean#L3-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/OrbitFinite.lean#L3-L26

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_OrbitFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qf32.orbit_finite :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {G : Type}
    [inst_2 : Group G] [inst_3 : TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (K : Subgroup G),
    IsCompact (↑K : Set G) →
      ∀ (w : V),
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) w = w} →
          {x : V | ∃ k ∈ K, ((ρ : G → V →ₗ[ℂ] V) k : V → V) w = x}.Finite := by sorry
