-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_re__fe5349d94a38
-- name    : P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_re__fe5349d94a38
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:51.029407+00:00
-- url     : https://prove2.me/theorems/5c7e0166-ab24-473a-9ec7-454799f8e42e
-- title:
--   P2 M PI Unitary Group Mass Formula Unit Det Root theta re  fe5349d94a38: P2 M PI Unitary Group Mass Formula Unit Det Root theta re  fe5349d94a38
-- statement:
--   The P2 M PI Unitary Group Mass Formula Unit Det Root theta re  fe5349d94a38 construction uses the P2 M PI Unitary Group Mass Formula Unit Det Root theta re  fe5349d94a38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L28-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
variable {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}

theorem P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_re__fe5349d94a38 : (UnitDetRootDefs.cmTheta b d).re = (b : ℝ) / 2 := by sorry

alias «PI».«UnitaryGroupMassFormula».«UnitDetRoot».«theta_re'» := P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_re__fe5349d94a38
