-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_ComplementSubspace_main
-- name    : UpperTheory.Reformulated.B.ComplementSubspace.main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:38:20.67612+00:00
-- url     : https://prove2.me/theorems/a241ba4d-dffd-4edd-9524-30b90f3756f1
-- title:
--   Complement Subspace: main
-- statement:
--   The Complement Subspace construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ComplementSubspace.lean#L23-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ComplementSubspace.lean#L23-L52

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ComplementSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open ComplementBasis

theorem UpperTheory.Reformulated.B.ComplementSubspace.main :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (U : Submodule K (Fin n → K)),
      ∃ (c : Matrix (Fin (Module.finrank K ↥U)) (Fin n) K) (a : Matrix (Fin n) (Fin n) K),
        (LinearIndependent K c ∧ Submodule.span K (Set.range c) = U) ∧ UpperTheory.Reformulated.B.ComplementSubspace.IsCompl c a := by sorry
