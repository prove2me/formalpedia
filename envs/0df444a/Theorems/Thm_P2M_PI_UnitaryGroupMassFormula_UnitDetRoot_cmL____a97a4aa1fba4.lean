-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____a97a4aa1fba4
-- name    : P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____a97a4aa1fba4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:43:09.664297+00:00
-- url     : https://prove2.me/theorems/5266a3fc-2a0f-41ac-af7c-8153a76cdaf1
-- title:
--   P2 M PI Unitary Group Mass Formula Unit Det Root cm L    a97a4aa1fba4: P2 M PI Unitary Group Mass Formula Unit Det Root cm L    a97a4aa1fba4
-- statement:
--   The P2 M PI Unitary Group Mass Formula Unit Det Root cm L    a97a4aa1fba4 construction uses the P2 M PI Unitary Group Mass Formula Unit Det Root cm L    a97a4aa1fba4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L14-L14

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

theorem P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____a97a4aa1fba4 : (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₁ = lam * a := by sorry

alias «PI».«UnitaryGroupMassFormula».«UnitDetRoot».«cmL_ω₁» := P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____a97a4aa1fba4
