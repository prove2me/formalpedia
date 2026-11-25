-- Prove2me | Theorems.Thm_PI_KerTens_W_tens_eq
-- name    : PI.KerTens.W.tens_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:53.329145+00:00
-- url     : https://prove2.me/theorems/5b2e234c-c206-4a39-a70e-e68d5a3eb060
-- title:
--   W: tens eq
-- statement:
--   The W construction uses the tens eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorSpanning/TensSpans.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorSpanning/TensSpans.lean#L61-L64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_TensSpans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open PI PI.KerTens PI.KerTens.W
open Formalism.L2.Th1.H (Sesq matH alphaQ qOf opU Th fixedBy)

theorem PI.KerTens.W.tens_eq {n : Type} (θ : (n → ℂ) → ℂ) (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) :
    tensPow θ N N' z = ∏ b : Fin N' × Fin N, θ (part z b) := by sorry
