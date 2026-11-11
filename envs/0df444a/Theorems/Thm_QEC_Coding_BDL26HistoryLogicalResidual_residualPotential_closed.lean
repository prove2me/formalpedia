-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_residualPotential_closed
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.residualPotential_closed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T19:05:53.785548+00:00
-- url     : https://prove2.me/theorems/fdc3eb43-6510-4ef1-87b2-d458d5816021
-- title:
--   BDL26 History Logical Residual: residual Potential closed
-- statement:
--   The BDL26 History Logical Residual construction uses the residual Potential closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Words.lean#L116-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Words.lean#L116-L119

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryLogicalResidual.residualPotential_closed (e u : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    (SuffixData S n).family.coboundary1 (TopIndex n)
      ((SuffixData S n).family.coboundary0 (TopIndex n) (residualPotential S n e u)) = 0 := by sorry
