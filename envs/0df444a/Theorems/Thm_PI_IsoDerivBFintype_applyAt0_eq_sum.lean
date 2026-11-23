-- Prove2me | Theorems.Thm_PI_IsoDerivBFintype_applyAt0_eq_sum
-- name    : PI.IsoDerivBFintype.applyAt0_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:19.650902+00:00
-- url     : https://prove2.me/theorems/71548d47-d729-4060-9752-79c6790b6e21
-- title:
--   Iso Deriv BFintype: apply At0 eq sum
-- statement:
--   The Iso Deriv BFintype construction uses the apply At0 eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean#L22-L32

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

theorem PI.IsoDerivBFintype.applyAt0_eq_sum (P : MvPolynomial (Idx T N N') ℂ) (S : Finset (Mono T N N'))
    (hS : P.support ⊆ S) : applyAt0 P Θ = ∑ α ∈ S, MvPolynomial.coeff α P * wt Θ α := by sorry
