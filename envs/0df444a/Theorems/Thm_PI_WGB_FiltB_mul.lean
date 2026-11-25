-- Prove2me | Theorems.Thm_PI_WGB_FiltB_mul
-- name    : PI.WGB.FiltB_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:57.232589+00:00
-- url     : https://prove2.me/theorems/a356c5f8-71d6-41ee-893c-ce66f6f74d82
-- title:
--   WGB: Filt B mul
-- statement:
--   The WGB construction uses the Filt B mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/DetPowUnitriB.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/DetPowUnitriB.lean#L26-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial

theorem PI.WGB.FiltB_mul {σ : Type*} (ψ : σ → ℕ) {d d' : ℕ} {p q : MvPolynomial σ ℂ} (hp : p ∈ FiltB ψ d)
    (hq : q ∈ FiltB ψ d') : p * q ∈ FiltB ψ (d + d') := by sorry
