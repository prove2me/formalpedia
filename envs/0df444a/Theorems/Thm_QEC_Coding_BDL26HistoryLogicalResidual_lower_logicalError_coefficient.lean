-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_lower_logicalError_coefficient
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.lower_logicalError_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:49:25.280503+00:00
-- url     : https://prove2.me/theorems/b85c2d68-581a-43b8-bf41-142f26b12431
-- title:
--   BDL26 History Logical Residual: lower logical Error coefficient
-- statement:
--   The BDL26 History Logical Residual construction uses the lower logical Error coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L174-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L174-L179

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryLogicalResidual.lower_logicalError_coefficient (sigma : TopInput S n)
    (u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    lowerCoefficient S n sigma (logicalError S n) u hu = 1 := by sorry
