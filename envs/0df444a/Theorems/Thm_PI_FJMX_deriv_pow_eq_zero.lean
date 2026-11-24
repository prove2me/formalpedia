-- Prove2me | Theorems.Thm_PI_FJMX_deriv_pow_eq_zero
-- name    : PI.FJMX.deriv_pow_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:44.199674+00:00
-- url     : https://prove2.me/theorems/578e2394-0e5b-45c5-8707-3c76723779c3
-- title:
--   FJMX: deriv pow eq zero
-- statement:
--   The FJMX construction uses the deriv pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L23-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.FJMX
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem PI.FJMX.deriv_pow_eq_zero (D : Derivation R A A) (a : A) (n : ℕ) (h : D a = 0) :
    D (a ^ n) = 0 := by sorry
