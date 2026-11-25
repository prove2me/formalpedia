-- Prove2me | Theorems.Thm_QH_meanSq_abs
-- name    : QH.meanSq_abs
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:07:19.433855+00:00
-- url     : https://prove2.me/theorems/5a65a36a-d28f-4fa5-8a09-c2236f766e96
-- title:
--   QH: mean Sq abs
-- statement:
--   The QH construction uses the mean Sq abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/MeanSqAbs.lean#L8-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/MeanSqAbs.lean#L8-L58

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMain
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_MeanSqAbs
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

theorem QH.meanSq_abs :
    ∀ (P : Finset ℕ) (m₀ a₀ nstar : ℕ) (Z y η B : ℝ) (κ : ℕ → ℂ), 8 ∣ m₀ → a₀.Coprime m₀ → 0 ≤ y → 0 ≤ η →
      (∀ q ∈ P, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ ⌊Z⌋₊ ^ 2 < q) → (∀ n, ‖κ n‖ ≤ 1) → (∀ p, sP (cN y) ⌊Z⌋₊ p ≤ B) →
      (∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → s ≤ ⌊Z⌋₊ ^ 2 → s ≠ nstar →
        |∑ q ∈ P, (jacobiSym (q : ℤ) s : ℝ)| ≤ η * P.card) →
      ∑ q ∈ P, ‖S Z y q κ‖ ^ 2 ≤ ((∑ p ∈ (Icc 1 ⌊Z⌋₊).filter Nat.Prime, sP (cN y) ⌊Z⌋₊ p ^ 2) + RR (cN y) m₀ ⌊Z⌋₊ ^ 2 +
        (2 * B ^ 2 + 2 * B * RR (cN y) m₀ ⌊Z⌋₊) + η * (∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n) ^ 2) * P.card := by sorry
