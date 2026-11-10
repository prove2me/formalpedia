-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCosetKet_fixed_Z
-- name    : QEC.Distillation.Ngu24Binary.binaryCosetKet_fixed_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:50:03.066733+00:00
-- url     : https://prove2.me/theorems/02a56f5b-36f8-4731-8bee-17cef2720e23
-- title:
--   Ngu24 Binary: binary Coset Ket fixed Z
-- statement:
--   The Ngu24 Binary construction uses the binary Coset Ket fixed Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L179-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L179-L193

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryCSSFieldWordFintype

theorem QEC.Distillation.Ngu24Binary.binaryCosetKet_fixed_Z (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (z : Word (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512))
    (hz : z ∈ (binaryZCode i).carrier) :
    PauliSymplectic.toQubitOperator (PauliSymplectic.cssZCheck z)
      (binaryCosetKet i u) = binaryCosetKet i u := by sorry
