-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_mem_stdLat_iff
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.mem_stdLat_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:12:45.33627+00:00
-- url     : https://prove2.me/theorems/8269c849-1267-49c7-87e1-635f52c92eb3
-- title:
--   Unimod Loc Std: mem std Lat iff
-- statement:
--   The Unimod Loc Std construction uses the mem std Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/CommOfBounded.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/CommOfBounded.lean#L17-L19

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.mem_stdLat_iff (L : PeriodPair) (v : m → ℂ) : v ∈ stdLat L m ↔ ∀ i, v i ∈ L.lattice := by sorry
