-- Prove2me | Theorems.Thm_QH_psi_thin
-- name    : QH.psi_thin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:06:44.813122+00:00
-- url     : https://prove2.me/theorems/64d58da7-a5c2-5a5e-8d89-7624eb63ed99
-- title:
--   QH: psi thin
-- statement:
--   The QH construction uses the psi thin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/PsiThin.lean#L385-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/PsiThin.lean#L385-L421

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_PeriodIntegrals_ExplicitFormulaCounts_ExplicitFormula
import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplex
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PsiThin
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

theorem QH.psi_thin :
    ∀ c₀ : ℝ, 0 < c₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (lam : ℝ), χ.IsPrimitive → 1 ≤ lam → Real.log N ≤ lam →
      (χ ^ 2 = 1 → χ ≠ 1 → NoExc c₀ χ) → ∀ u : ℝ, Real.exp 1 ≤ u →
        ‖PI.psi0 χ u‖ ≤ C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))) := by sorry
