-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_fiveSiteSingleLogical_intertwines_encoding
-- name    : QEC.Distillation.KT19PrimeQuditCSS.fiveSiteSingleLogical_intertwines_encoding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:42:44.675346+00:00
-- url     : https://prove2.me/theorems/f770110f-3641-4a7e-92ff-3e63096983c2
-- title:
--   KT19 Prime Qudit CSS: five Site Single Logical intertwines encoding
-- statement:
--   The p=5 fixture has the generic full encoder-commuting equation on one literal qudit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1297-L1309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L1297-L1309

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] primeQuditRegisterLabelFintype

theorem QEC.Distillation.KT19PrimeQuditCSS.fiveSiteSingleLogical_intertwines_encoding (psi : PrimeQudit 5) :
    fiveSiteSingleLogical.physicalU13 (fiveSiteSingleLogical.encodedCode.encode psi) =
      fiveSiteSingleLogical.encodedCode.encode (fiveSiteSingleLogical.logicalInverseU13 psi) := by sorry
