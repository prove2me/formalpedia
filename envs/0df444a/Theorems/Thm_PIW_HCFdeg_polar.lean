-- Prove2me | Theorems.Thm_PIW_HCFdeg_polar
-- name    : PIW.HCFdeg.polar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:47:55.94002+00:00
-- url     : https://prove2.me/theorems/30845366-2d6f-4611-b0b5-1fa1817f3180
-- title:
--   HCFdeg: polar
-- statement:
--   The HCFdeg construction uses the polar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/Unimod.lean#L160-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/Unimod.lean#L160-L223

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise
variable {n : ℕ} (ε : Fin n → Bool)

theorem PIW.HCFdeg.polar (g : UJ ε) : ∃ s : UJ ε, (toM s)ᴴ = toM s ∧ g * s⁻¹ ∈ KG ε := by sorry
