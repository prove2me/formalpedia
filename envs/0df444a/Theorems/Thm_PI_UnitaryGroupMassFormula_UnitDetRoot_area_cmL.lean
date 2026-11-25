-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_area_cmL
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.area_cmL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:52.933803+00:00
-- url     : https://prove2.me/theorems/ee8a0be9-138a-4443-a82c-966495748972
-- title:
--   Unit Det Root: area cm L
-- statement:
--   The Unit Det Root construction uses the area cm L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L32-L43

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

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.area_cmL : UnitDetRootDefs.area (UnitDetRootDefs.cmL a b d ha hd lam hlam) = Complex.normSq lam * a * (Real.sqrt d / 2) := by sorry
