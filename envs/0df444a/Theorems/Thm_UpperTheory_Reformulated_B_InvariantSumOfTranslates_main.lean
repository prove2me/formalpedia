-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_InvariantSumOfTranslates_main
-- name    : UpperTheory.Reformulated.B.InvariantSumOfTranslates.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:32:18.397168+00:00
-- url     : https://prove2.me/theorems/ad607f06-3d4e-49bb-8a11-3e3db098e1c2
-- title:
--   Invariant Sum Of Translates: main
-- statement:
--   The Invariant Sum Of Translates construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DeRhamEllipticIdentity.lean#L3-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DeRhamEllipticIdentity.lean#L3-L55

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DeRhamEllipticIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.InvariantSumOfTranslates.main :
    ∀ {K S : Type} [inst : Group K] [inst_1 : TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [inst_4 : AddCommGroup S] [inst_5 : _root_.Module ℂ S] (ω : K →* Module.End ℂ S) (f₀ : S),
      (∃ U ∈ nhds (1 : K), ∀ k ∈ U, ((ω : K → Module.End ℂ S) k : S → S) f₀ = f₀) →
        ∃ (m : ℕ) (k : Fin (m + (1 : ℕ)) → K),
          ∀ (g : K),
            ((ω : K → Module.End ℂ S) g : S → S) (∑ i : Fin (m + (1 : ℕ)), ((ω : K → Module.End ℂ S) (k i) : S → S) f₀) =
              ∑ i : Fin (m + (1 : ℕ)), ((ω : K → Module.End ℂ S) (k i) : S → S) f₀ := by sorry
