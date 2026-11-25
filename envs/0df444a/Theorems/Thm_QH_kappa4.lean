-- Prove2me | Theorems.Thm_QH_kappa4
-- name    : QH.kappa4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:06:31.700689+00:00
-- url     : https://prove2.me/theorems/0c8a9315-8ea1-40ec-b14c-39202f4910c9
-- title:
--   QH: kappa4
-- statement:
--   The QH construction uses the kappa4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean#L126-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/Kappa4Loglog.lean#L126-L153

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailFinal
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mertensUpper
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_Kappa4Loglog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH

theorem QH.kappa4 :
    ∀ ε A : ℝ, 0 < ε → ε < 1 / 52 → 0 < A → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ A * Y ^ (ε / 5) * Real.log Y ^ 2 → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ 4 * Real.log Y := by sorry
