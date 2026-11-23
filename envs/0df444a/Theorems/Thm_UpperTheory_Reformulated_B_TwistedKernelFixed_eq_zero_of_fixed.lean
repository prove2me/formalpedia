-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_TwistedKernelFixed_eq_zero_of_fixed
-- name    : UpperTheory.Reformulated.B.TwistedKernelFixed.eq_zero_of_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:56.688257+00:00
-- url     : https://prove2.me/theorems/e76a3aa1-d47f-4686-809b-763399bd84d3
-- title:
--   Twisted Kernel Fixed: eq zero of fixed
-- statement:
--   The Twisted Kernel Fixed construction uses the eq zero of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TwistedKernelFixed.lean#L80-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TwistedKernelFixed.lean#L80-L138

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.TwistedKernelFixed.eq_zero_of_fixed :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] {π : Representation ℂ G V}
      [inst_3 : TopologicalSpace G] [IsTopologicalGroup G],
      UpperTheory.Reformulated.B.TwistedKernelFixed.IsSmooth π →
        ∀ {H : Subgroup G},
          IsCompact (↑H : Set G) →
            ∀ {v : V}, v ∈ UpperTheory.Reformulated.B.TwistedKernelFixed.fixed π H → v ∈ UpperTheory.Reformulated.B.TwistedKernelFixed.twKer π H (1 : ↥H →* ℂˣ) → v = (0 : V) := by sorry
