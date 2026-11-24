-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_im__25f4bf5b8973
-- name    : P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_im__25f4bf5b8973
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:56.344278+00:00
-- url     : https://prove2.me/theorems/e240dd6a-e148-40e5-b8f3-46d457b2e020
-- title:
--   P2 M PI Unitary Group Mass Formula Unit Det Root theta im  25f4bf5b8973: P2 M PI Unitary Group Mass Formula Unit Det Root theta im  25f4bf5b8973
-- statement:
--   The P2 M PI Unitary Group Mass Formula Unit Det Root theta im  25f4bf5b8973 construction uses the P2 M PI Unitary Group Mass Formula Unit Det Root theta im  25f4bf5b8973 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L30-L30

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

theorem P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_im__25f4bf5b8973 : (UnitDetRootDefs.cmTheta b d).im = Real.sqrt d / 2 := by sorry

alias «PI».«UnitaryGroupMassFormula».«UnitDetRoot».«theta_im'» := P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_im__25f4bf5b8973
