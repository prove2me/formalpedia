-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qe13_det_emb_unitri_A
-- name    : UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:09.883893+00:00
-- url     : https://prove2.me/theorems/29246816-4e8a-4cc9-8b62-fd0ff74ab554
-- title:
--   Qe13: det emb unitri A
-- statement:
--   The Qe13 construction uses the det emb unitri A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DetEmbUnitriA.lean#L43-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DetEmbUnitriA.lean#L43-L59

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A :
    ∀ {n : ℕ} (g : GL (Fin n) ℂ),
      (∀ (i j : Fin n), j < i → (↑g : Matrix (Fin n) (Fin n) ℂ) i j = (0 : ℂ)) →
        (∀ (i : Fin n), (↑g : Matrix (Fin n) (Fin n) ℂ) i i = (1 : ℂ)) →
          (Matrix.GeneralLinearGroup.det : GL (Fin (n + (1 : ℕ))) ℂ → ℂˣ)
              ((UpperTheory.Reformulated.B.Qe13.embGL ℂ n (n + (1 : ℕ)) rfl : GL (Fin n) ℂ → GL (Fin (n + (1 : ℕ))) ℂ) g) =
            (1 : ℂˣ) := by sorry
