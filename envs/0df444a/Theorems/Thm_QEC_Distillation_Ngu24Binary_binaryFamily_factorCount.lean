-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryFamily_factorCount
-- name    : QEC.Distillation.Ngu24Binary.binaryFamily_factorCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:39:24.748705+00:00
-- url     : https://prove2.me/theorems/f58d1af0-5612-4f33-a10d-69c130cbba0e
-- title:
--   Ngu24 Binary: binary Family factor Count
-- statement:
--   The factor count of the actual physical product equals the number of selected triples.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryFamily.lean#L66-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryFamily.lean#L66-L69

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

theorem QEC.Distillation.Ngu24Binary.binaryFamily_factorCount (i : Nat) :
    (binaryPhysicalFactorization (J := (f256SourceInput i).PivotComplement)).factorCount =
      (binarySelectedSites (f256SourceInput i).PivotComplement).card := by sorry
