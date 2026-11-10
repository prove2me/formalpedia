-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryFamily_selected_density
-- name    : QEC.Distillation.Ngu24Binary.binaryFamily_selected_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:37:30.516734+00:00
-- url     : https://prove2.me/theorems/7fce1cb7-600b-48a8-95e3-4001f14a4902
-- title:
--   Ngu24 Binary: binary Family selected density
-- statement:
--   The fixed selected-triple fraction uses the entire physical length of one block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryFamily.lean#L60-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryFamily.lean#L60-L63

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter

theorem QEC.Distillation.Ngu24Binary.binaryFamily_selected_density (i : Nat) :
    (binaryLength i : ℚ) / 512 ≤ (binarySelectedSites (f256SourceInput i).PivotComplement).card := by sorry
