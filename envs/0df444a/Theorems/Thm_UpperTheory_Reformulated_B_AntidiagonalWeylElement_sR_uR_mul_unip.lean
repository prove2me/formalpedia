-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_AntidiagonalWeylElement_sR_uR_mul_unip
-- name    : UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR_uR_mul_unip
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:08.857312+00:00
-- url     : https://prove2.me/theorems/d5f24908-57ac-4beb-8218-cc2f45ec6e2c
-- title:
--   Antidiagonal Weyl Element: s R u R mul unip
-- statement:
--   The Antidiagonal Weyl Element construction uses the s R u R mul unip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UnitaryRootEmbedding.lean#L826-L854
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UnitaryRootEmbedding.lean#L826-L854

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryRootEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR_uR_mul_unip :
    ∀ (L : Type) [inst : Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
      (hσ : ∀ (x : L), (σ : L → L) ((σ : L → L) x) = x) (a : ℕ) (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n)
      (v : ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n)),
      UpperTheory.Reformulated.B.AntidiagonalWeylElement.IsUnipU v →
        ∃ (y : L),
          ∀ (x : L),
            ∃ (b : ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n)),
              UpperTheory.Reformulated.B.AntidiagonalWeylElement.IsUnipU b ∧
                UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR σ hσ a h * UpperTheory.Reformulated.B.AntidiagonalWeylElement.uR σ hσ a h x * v =
                  b * (UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR σ hσ a h * UpperTheory.Reformulated.B.AntidiagonalWeylElement.uR σ hσ a h (x + y)) := by sorry
