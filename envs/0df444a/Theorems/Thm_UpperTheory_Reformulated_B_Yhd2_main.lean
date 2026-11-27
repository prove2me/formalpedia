-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yhd2_main
-- name    : UpperTheory.Reformulated.B.Yhd2.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:04:46.66314+00:00
-- url     : https://prove2.me/theorems/f5709216-7058-5ab5-9525-623a795ee514
-- title:
--   Yhd2: main
-- statement:
--   The Yhd2 construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsRestTail.lean#L3-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsRestTail.lean#L3-L21

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsRestTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Yhd2.main :
    ∀ {G M : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
      [inst_4 : AddCommGroup M] [inst_5 : _root_.Module ℂ M] (ρ : Representation ℂ G M) (x : M),
      IsOpen {g : G | ((ρ : G → M →ₗ[ℂ] M) g : M → M) x = x} →
        (Set.range fun (g : G) ↦ ((ρ : G → M →ₗ[ℂ] M) g : M → M) x).Countable := by sorry
