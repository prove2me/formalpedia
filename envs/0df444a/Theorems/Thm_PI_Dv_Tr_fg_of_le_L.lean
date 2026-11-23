-- Prove2me | Theorems.Thm_PI_Dv_Tr_fg_of_le_L
-- name    : PI.Dv.Tr.fg_of_le_L
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:10.432802+00:00
-- url     : https://prove2.me/theorems/fa4b0492-cacb-4c17-ab30-9909cd0366fa
-- title:
--   Tr: fg of le L
-- statement:
--   The Tr construction uses the fg of le L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/FgOfLeL.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/FgOfLeL.lean#L19-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_FgOfLeL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

theorem PI.Dv.Tr.fg_of_le_L (A : Formalism.BasicNotions.HLat K) (hA : A.Good) (M : Submodule (𝓞 K) A.V) (hM : M ≤ A.L) : M.FG := by sorry
