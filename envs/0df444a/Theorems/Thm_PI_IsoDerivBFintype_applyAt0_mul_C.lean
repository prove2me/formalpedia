-- Prove2me | Theorems.Thm_PI_IsoDerivBFintype_applyAt0_mul_C
-- name    : PI.IsoDerivBFintype.applyAt0_mul_C
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:09:07.57826+00:00
-- url     : https://prove2.me/theorems/ea77de07-a237-5040-a8b4-4993af2e698f
-- title:
--   Iso Deriv BFintype: apply At0 mul C
-- statement:
--   The Iso Deriv BFintype construction uses the apply At0 mul C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L56-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.IsoDerivBFintype
open PI.IsoDerivB
variable {T : Type} [Fintype T] {N N' : ℕ} (Θ : VC T N N' → ℂ)

theorem PI.IsoDerivBFintype.applyAt0_mul_C (c : ℂ) (P : MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (P * MvPolynomial.C c) Θ = applyAt0 P Θ * c := by sorry
