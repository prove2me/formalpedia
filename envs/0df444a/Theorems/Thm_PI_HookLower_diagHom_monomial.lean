-- Prove2me | Theorems.Thm_PI_HookLower_diagHom_monomial
-- name    : PI.HookLower.diagHom_monomial
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:06:17.437414+00:00
-- url     : https://prove2.me/theorems/9b93e93d-f871-5c0f-88e0-8bbb9b9447c0
-- title:
--   Hook Lower: diag Hom monomial
-- statement:
--   The Hook Lower construction uses the diag Hom monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DiagonalMonomialFactorial.lean#L16-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DiagonalMonomialFactorial.lean#L16-L34

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookLower
open scoped Classical

theorem PI.HookLower.diagHom_monomial {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (c : ℚ) :
    diagHom N (monomial m c) = if IsDiag m then monomial m c else 0 := by sorry
