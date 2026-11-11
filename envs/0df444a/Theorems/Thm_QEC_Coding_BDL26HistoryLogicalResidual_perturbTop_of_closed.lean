-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_perturbTop_of_closed
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.perturbTop_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:43:44.834286+00:00
-- url     : https://prove2.me/theorems/239443c3-2127-4074-8b56-5168a56ebbb8
-- title:
--   BDL26 History Logical Residual: perturb Top of closed
-- statement:
--   The BDL26 History Logical Residual construction uses the perturb Top of closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Words.lean#L138-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Words.lean#L138-L144

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.perturbTop_of_closed (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n))
    (he : (SuffixData S n).family.coboundary1 (TopIndex n) e = 0) :
    perturbTop S n sigma e = sigma := by sorry
