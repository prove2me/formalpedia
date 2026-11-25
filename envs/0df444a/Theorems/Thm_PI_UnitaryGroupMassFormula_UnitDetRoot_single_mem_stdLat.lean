-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_single_mem_stdLat
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.single_mem_stdLat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:40:26.006961+00:00
-- url     : https://prove2.me/theorems/671b4d9e-4693-5fbf-8dcf-b79eac5e64fa
-- title:
--   Unit Det Root: single mem std Lat
-- statement:
--   The Unit Det Root construction uses the single mem std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/DetMemOfEntries.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/DetMemOfEntries.lean#L18-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
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

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.single_mem_stdLat {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [DecidableEq m] (j : m) :
    Pi.single j (lam * a) ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m := by sorry
