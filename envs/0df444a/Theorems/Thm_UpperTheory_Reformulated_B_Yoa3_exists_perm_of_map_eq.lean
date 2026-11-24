-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yoa3_exists_perm_of_map_eq
-- name    : UpperTheory.Reformulated.B.Yoa3.exists_perm_of_map_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:04:03.615442+00:00
-- url     : https://prove2.me/theorems/eebf825f-b323-464c-bdfb-8e6a703bdfb7
-- title:
--   Yoa3: exists perm of map eq
-- statement:
--   The Yoa3 construction uses the exists perm of map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsSideLast.lean#L3-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsSideLast.lean#L3-L26

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsSideLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Yoa3.exists_perm_of_map_eq :
    ∀ {n : ℕ} {z z' : Fin n → ℂˣ},
      Multiset.map (fun (i : Fin n) ↦ (↑(z i) : ℂ)) Finset.univ.val =
          Multiset.map (fun (i : Fin n) ↦ (↑(z' i) : ℂ)) Finset.univ.val →
        ∃ (σ : Equiv.Perm (Fin n)), z' = z ∘ (⇑σ : Fin n → Fin n) := by sorry
