-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_mem_stdLat
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.mem_stdLat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:12.11228+00:00
-- url     : https://prove2.me/theorems/51aa28ae-3407-42d0-b94a-495da62021da
-- title:
--   Unit Det Root: mem std Lat
-- statement:
--   The Unit Det Root construction uses the mem std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L25-L26

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

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.mem_stdLat {m : Type} {L : PeriodPair} {x : m → ℂ} : x ∈ UnitDetRootDefs.stdLat L m ↔ ∀ i, x i ∈ L.lattice := by sorry
