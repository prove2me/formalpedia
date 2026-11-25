-- Prove2me | Theorems.Thm_PI_IsoScaleA_UnitaryGroupMassFormula_applyAt0_C_mul
-- name    : PI.IsoScaleA.UnitaryGroupMassFormula.applyAt0_C_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:45.486945+00:00
-- url     : https://prove2.me/theorems/209d51d9-d23b-497d-98e0-2feb9676975e
-- title:
--   Unitary Group Mass Formula: apply At0 C mul
-- statement:
--   The Unitary Group Mass Formula construction uses the apply At0 C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryScaleCount/CardEqSumColLen.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryScaleCount/CardEqSumColLen.lean#L56-L66

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoScaleA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryScaleCount_CardEqSumColLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoScaleA PI.IsoScaleA.UnitaryGroupMassFormula
open PI.IsoScaleA

theorem PI.IsoScaleA.UnitaryGroupMassFormula.applyAt0_C_mul {T : Type} [Fintype T] {N N' : ℕ} (a : ℂ) (P : MvPolynomial (Idx T N N') ℂ)
    (G : VC T N N' → ℂ) : applyAt0 (MvPolynomial.C a * P) G = a * applyAt0 P G := by sorry
