-- Prove2me | Theorems.Thm_PI_HookLower_diagHom_lpMinor
-- name    : PI.HookLower.diagHom_lpMinor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:06:28.370008+00:00
-- url     : https://prove2.me/theorems/1002ec91-bcec-55f1-8ef6-a2775f17f494
-- title:
--   Hook Lower: diag Hom lp Minor
-- statement:
--   The Hook Lower construction uses the diag Hom lp Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DiagonalMonomialFactorial.lean#L51-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DiagonalMonomialFactorial.lean#L51-L68

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

theorem PI.HookLower.diagHom_lpMinor {N : ℕ} (s : ℕ) (hr hn : s ≤ N) :
    diagHom N (lpMinor ℚ s hr hn) = monomial (diagMono s hr) 1 := by sorry
