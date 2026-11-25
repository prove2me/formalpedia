-- Prove2me | Theorems.Thm_QH_box_of_S
-- name    : QH.box_of_S
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:00.431263+00:00
-- url     : https://prove2.me/theorems/20b0345d-1a05-53cf-91ab-eefb8311d459
-- title:
--   QH: box of S
-- statement:
--   The QH construction uses the box of S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean#L28-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/BoxOfS.lean#L28-L60

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_TailKExp
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_kappaC
import Definitions.Def_Formalism_GL3MeanSquares_ZeroFreeRegionGl2PrimeChoiceResults
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_BoxOfS
import Theorems.Thm_QH_kappaC

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

theorem QH.box_of_S :
    ∃ C : ℝ, 0 < C ∧ ∀ ε τ K : ℝ, 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (q : ℕ) (κ : ℕ → ℂ),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) → GoodC Q χ → (∀ n : ℕ, χ (n : ZMod N) = κ n * J q n) →
      (∀ y ∈ Set.Icc Y (Y ^ K), ‖S ((Y ^ K) ^ 400) y q κ‖ ≤ y ^ (1 / 2 + τ) / 2) → Box Q C τ Y (Y ^ K) χ := by sorry
