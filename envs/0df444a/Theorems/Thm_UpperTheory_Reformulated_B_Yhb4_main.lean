-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yhb4_main
-- name    : UpperTheory.Reformulated.B.Yhb4.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:23:01.035705+00:00
-- url     : https://prove2.me/theorems/166f5e99-56e9-48b2-b6d7-d28643c0a208
-- title:
--   Yhb4: main
-- statement:
--   The Yhb4 construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SmulNn.lean#L13-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SmulNn.lean#L13-L93

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure

theorem UpperTheory.Reformulated.B.Yhb4.main :
    ∀ {H N : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : IsTopologicalGroup H]
      [inst_3 : LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [inst_6 : MeasurableSpace H]
      [inst_7 : BorelSpace H] [inst_8 : Group N] [inst_9 : TopologicalSpace N] [inst_10 : IsTopologicalGroup N]
      [inst_11 : LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [inst_14 : MeasurableSpace N]
      [inst_15 : BorelSpace N] (ι : N →* H),
      Continuous (⇑ι : N → H) →
        ∀ (π : H → N),
          Continuous π →
            (∀ (x : N) (p : H), π ((ι : N → H) x * p) = x * π p) →
              ∀ (φ : H ≃ₜ* H) (ψ : N ≃ₜ* N),
                (∀ (p : H), π ((φ : H → H) p) = (ψ : N → N) (π p)) →
                  (∀ (p : H), ((ι : N → H) (π ((φ : H → H) p)))⁻¹ * (φ : H → H) p = ((ι : N → H) (π p))⁻¹ * p) →
                    MeasureTheory.mulEquivHaarChar φ = MeasureTheory.mulEquivHaarChar ψ := by sorry
