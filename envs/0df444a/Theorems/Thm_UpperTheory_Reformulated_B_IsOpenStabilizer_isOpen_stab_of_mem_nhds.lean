-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_IsOpenStabilizer_isOpen_stab_of_mem_nhds
-- name    : UpperTheory.Reformulated.B.IsOpenStabilizer.isOpen_stab_of_mem_nhds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:49:50.186723+00:00
-- url     : https://prove2.me/theorems/b62dcbf4-909b-459a-8e5c-77eea7df3924
-- title:
--   Is Open Stabilizer: is Open stab of mem nhds
-- statement:
--   The Is Open Stabilizer construction uses the is Open stab of mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsOpenStabilizer.lean#L3-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsOpenStabilizer.lean#L3-L25

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsOpenStabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.IsOpenStabilizer.isOpen_stab_of_mem_nhds :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
      {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} ∈ nhds (1 : G) →
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} := by sorry
