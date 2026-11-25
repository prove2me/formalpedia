-- Prove2me | Theorems.Thm_PI_TOW_fockB_apply
-- name    : PI.TOW.fockB_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:37:26.584821+00:00
-- url     : https://prove2.me/theorems/487772e0-2ea5-48a7-b2db-915dd67dee73
-- title:
--   TOW: fock B apply
-- statement:
--   The TOW construction uses the fock B apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L59-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L59-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
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
open PI PI.TOW
open PI.TO
variable {σ R : Type*} [CommRing R]

theorem PI.TOW.fockB_apply (f g : MvPolynomial σ R) : fockB σ R f g = fockR f g := by sorry
