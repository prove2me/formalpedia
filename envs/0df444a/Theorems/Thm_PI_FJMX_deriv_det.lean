-- Prove2me | Theorems.Thm_PI_FJMX_deriv_det
-- name    : PI.FJMX.deriv_det
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:14.745845+00:00
-- url     : https://prove2.me/theorems/d9b3f8c6-6229-4f61-be4b-af5c8763a877
-- title:
--   FJMX: deriv det
-- statement:
--   The FJMX construction uses the deriv det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L42-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L42-L59

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

theorem PI.FJMX.deriv_det {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A)
    (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateCol i (fun k => D (M k i))).det := by sorry
