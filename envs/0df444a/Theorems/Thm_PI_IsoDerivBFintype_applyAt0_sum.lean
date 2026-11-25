-- Prove2me | Theorems.Thm_PI_IsoDerivBFintype_applyAt0_sum
-- name    : PI.IsoDerivBFintype.applyAt0_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:09:14.533015+00:00
-- url     : https://prove2.me/theorems/e1a0cfe9-8fef-5985-b2d5-99f8aef2d357
-- title:
--   Iso Deriv BFintype: apply At0 sum
-- statement:
--   The Iso Deriv BFintype construction uses the apply At0 sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L60-L65

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

theorem PI.IsoDerivBFintype.applyAt0_sum {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (∑ i ∈ s, P i) Θ = ∑ i ∈ s, applyAt0 (P i) Θ := by sorry
