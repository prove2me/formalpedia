-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qf33_uniq
-- name    : UpperTheory.Reformulated.B.Qf33.uniq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:03.502521+00:00
-- url     : https://prove2.me/theorems/6f410686-4ef8-4944-8e19-11a05166cc6b
-- title:
--   Qf33: uniq
-- statement:
--   The Qf33 construction uses the uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BlockDiagonalLeviEmbedding.lean#L239-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BlockDiagonalLeviEmbedding.lean#L239-L279

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlockDiagonalLeviEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical

theorem UpperTheory.Reformulated.B.Qf33.uniq :
    ∀ {R : Type} [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : Fintype α] [inst_2 : LinearOrder α]
      [inst_3 : (a : α) → Fintype (m a)] [inst_4 : (a : α) → DecidableEq (m a)] [inst_5 : Fintype n]
      [inst_6 : DecidableEq n] {e : (a : α) × m a ≃ n},
      ∀ a ∈ UpperTheory.Reformulated.B.Qf33.unipRadLower R e,
        ∀ a' ∈ UpperTheory.Reformulated.B.Qf33.unipRadLower R e,
          ∀ b ∈ (UpperTheory.Reformulated.B.Qf33.leviEmb R e).range,
            ∀ b' ∈ (UpperTheory.Reformulated.B.Qf33.leviEmb R e).range,
              ∀ c ∈ UpperTheory.Reformulated.B.Qf33.unipRad R e,
                ∀ c' ∈ UpperTheory.Reformulated.B.Qf33.unipRad R e, a * b * c = a' * b' * c' → a = a' ∧ b = b' ∧ c = c' := by sorry
