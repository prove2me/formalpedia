-- Prove2me | Theorems.Thm_PI_FJMX_deriv_prod_eq_zero
-- name    : PI.FJMX.deriv_prod_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:44.180001+00:00
-- url     : https://prove2.me/theorems/b720304f-c929-4e13-bd72-e8ded3f93801
-- title:
--   FJMX: deriv prod eq zero
-- statement:
--   The FJMX construction uses the deriv prod eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L13-L21

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

theorem PI.FJMX.deriv_prod_eq_zero {ι : Type*} (D : Derivation R A A) (s : Finset ι) (f : ι → A)
    (h : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i) = 0 := by sorry
