-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yhc6_main
-- name    : UpperTheory.Reformulated.B.Yhc6.main
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:31.078217+00:00
-- url     : https://prove2.me/theorems/91b152d6-56c5-5bf0-9ad6-71ae948c5e9f
-- title:
--   Yhc6: main
-- statement:
--   The Yhc6 construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsRestSide.lean#L3-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsRestSide.lean#L3-L13

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsRestSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Yhc6.main :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {n : ℕ} (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) (m : ℕ),
      ((↑g : Matrix (Fin n) (Fin n) k) * x * (↑g⁻¹ : Matrix (Fin n) (Fin n) k)) ^ m =
        (↑g : Matrix (Fin n) (Fin n) k) * x ^ m * (↑g⁻¹ : Matrix (Fin n) (Fin n) k) := by sorry
