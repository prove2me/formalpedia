-- Prove2me | Theorems.Thm_PI_FJMX_deriv_det_eq_zero
-- name    : PI.FJMX.deriv_det_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:50.504018+00:00
-- url     : https://prove2.me/theorems/77608bc3-5c28-4d40-86e8-d9b09f1730f7
-- title:
--   FJMX: deriv det eq zero
-- statement:
--   The FJMX construction uses the deriv det eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L61-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L61-L77

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

theorem PI.FJMX.deriv_det_eq_zero {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A)
    (M : Matrix n n A)
    (h : ∀ i, (∀ k, D (M k i) = 0) ∨ ∃ i', i' ≠ i ∧ ∃ c : A, ∀ k, D (M k i) = c * M k i') :
    D M.det = 0 := by sorry
