-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
-- name    : QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:12:30.388346+00:00
-- url     : https://prove2.me/theorems/ce631a93-0a89-41cb-aad5-ef2689999e9c
-- title:
--   BDL26 Finite Alternating Core: finite Rz target val
-- statement:
--   The BDL26 Finite Alternating Core construction uses the finite Rz target val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L397-L398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L397-L398

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Mathlib.LinearAlgebra.StdBasis
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26FiniteAlternatingCore
open MultiscaleDecoder
open Module
attribute [instance] FiniteCochainCarrier.fintypeC0
attribute [instance] FiniteCochainCarrier.fintypeC1
attribute [instance] FiniteCochainCarrier.fintypeC2

theorem QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val (depth i : Nat) (h : 2 * i + 1 < depth) :
    (finiteRzStepIndex depth i h).succ.val = 2 * i + 2 := by sorry

attribute [defeq] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
