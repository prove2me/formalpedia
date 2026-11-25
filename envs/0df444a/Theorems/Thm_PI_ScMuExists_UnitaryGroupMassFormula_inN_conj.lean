-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inN_conj
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.inN_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:13:45.750795+00:00
-- url     : https://prove2.me/theorems/a8ff329c-e2f7-4445-8d10-8b686df1c3a6
-- title:
--   Unitary Group Mass Formula: in N conj
-- statement:
--   The Unitary Group Mass Formula construction uses the in N conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L140-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L140-L160

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ}

theorem PI.ScMuExists.UnitaryGroupMassFormula.inN_conj {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
    {h h' x : Matrix (Fin n) (Fin n) ℂ} (hU : Formalism.REAL.inUJ ε h) (hh : h * h' = 1) (hh' : h' * h = 1)
    (he : ∀ a, h *ᵥ e a = e a) (hz : h *ᵥ z = z) (hx : InN ε e z x) : InN ε e z (h * x * h') := by sorry
