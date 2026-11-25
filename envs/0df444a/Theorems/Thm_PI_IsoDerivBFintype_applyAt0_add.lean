-- Prove2me | Theorems.Thm_PI_IsoDerivBFintype_applyAt0_add
-- name    : PI.IsoDerivBFintype.applyAt0_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:49.037233+00:00
-- url     : https://prove2.me/theorems/a6ca4d51-ef94-57b4-a794-c4f472cd064f
-- title:
--   Iso Deriv BFintype: apply At0 add
-- statement:
--   The Iso Deriv BFintype construction uses the apply At0 add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L34-L40

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

theorem PI.IsoDerivBFintype.applyAt0_add (P Q : MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (P + Q) Θ = applyAt0 P Θ + applyAt0 Q Θ := by sorry
