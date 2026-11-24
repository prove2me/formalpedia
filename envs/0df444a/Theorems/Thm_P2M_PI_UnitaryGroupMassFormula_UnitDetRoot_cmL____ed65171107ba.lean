-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____ed65171107ba
-- name    : P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____ed65171107ba
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:43:12.627602+00:00
-- url     : https://prove2.me/theorems/131209eb-210e-4ab0-9746-6926420b70d2
-- title:
--   P2 M PI Unitary Group Mass Formula Unit Det Root cm L    ed65171107ba: P2 M PI Unitary Group Mass Formula Unit Det Root cm L    ed65171107ba
-- statement:
--   The P2 M PI Unitary Group Mass Formula Unit Det Root cm L    ed65171107ba construction uses the P2 M PI Unitary Group Mass Formula Unit Det Root cm L    ed65171107ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L16-L16

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

theorem P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____ed65171107ba : (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₂ = lam * UnitDetRootDefs.cmTheta b d := by sorry

alias «PI».«UnitaryGroupMassFormula».«UnitDetRoot».«cmL_ω₂» := P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____ed65171107ba
