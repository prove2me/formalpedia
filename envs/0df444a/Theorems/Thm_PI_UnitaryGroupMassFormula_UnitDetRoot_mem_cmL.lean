-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_mem_cmL
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.mem_cmL
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:38.81183+00:00
-- url     : https://prove2.me/theorems/48c880e7-a076-4635-9b75-4df3a40a7740
-- title:
--   Unit Det Root: mem cm L
-- statement:
--   The Unit Det Root construction uses the mem cm L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L18-L23

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

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.mem_cmL {x : ℂ} :
    x ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice ↔ ∃ p q : ℤ, x = lam * ((p : ℂ) * a + (q : ℂ) * UnitDetRootDefs.cmTheta b d) := by sorry
