-- Prove2me | Theorems.Thm_PI_IsoDerivBFintype_applyAt0_C_mul
-- name    : PI.IsoDerivBFintype.applyAt0_C_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:02.982273+00:00
-- url     : https://prove2.me/theorems/63e7cb02-05ca-427a-9940-4e8e5df483a2
-- title:
--   Iso Deriv BFintype: apply At0 C mul
-- statement:
--   The Iso Deriv BFintype construction uses the apply At0 C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L45-L54

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

theorem PI.IsoDerivBFintype.applyAt0_C_mul (c : ℂ) (P : MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (MvPolynomial.C c * P) Θ = c * applyAt0 P Θ := by sorry
