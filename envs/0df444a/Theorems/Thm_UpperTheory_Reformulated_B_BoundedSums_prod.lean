-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_BoundedSums_prod
-- name    : UpperTheory.Reformulated.B.BoundedSums.prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:38:22.662472+00:00
-- url     : https://prove2.me/theorems/78a3a859-e2f9-426b-9fba-5a899a7138e0
-- title:
--   Bounded Sums: prod
-- statement:
--   The Bounded Sums construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BoundedSums.lean#L43-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BoundedSums.lean#L43-L60

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BoundedSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.BoundedSums.prod :
    ∀ {C : Type} [inst : Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {σ ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C},
      (∀ i ∈ S, UpperTheory.Reformulated.B.BoundedSums.BddS V (f i)) → UpperTheory.Reformulated.B.BoundedSums.BddS V fun (n : ℕ) ↦ ∏ i ∈ S, f i n := by sorry
