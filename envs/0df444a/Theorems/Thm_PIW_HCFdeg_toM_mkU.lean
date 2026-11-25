-- Prove2me | Theorems.Thm_PIW_HCFdeg_toM_mkU
-- name    : PIW.HCFdeg.toM_mkU
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:00.83228+00:00
-- url     : https://prove2.me/theorems/b88c7354-0407-410e-914b-e8f575a22eeb
-- title:
--   HCFdeg: to M mk U
-- statement:
--   The HCFdeg construction uses the to M mk U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/Unimod.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/Unimod.lean#L79-L79

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

theorem PIW.HCFdeg.toM_mkU (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) : toM (mkU ε g hg) = g := by sorry
