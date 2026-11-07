-- Prove2me | Theorems.Thm_QEC_Coding_FinitePath_HammingWeight_single_le_one
-- name    : QEC.Coding.FinitePath.HammingWeight_single_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:09:11.598197+00:00
-- url     : https://prove2.me/theorems/04b38d6f-3f54-4095-9e5d-220990d561d0
-- title:
--   Finite Path: Hamming Weight single le one
-- statement:
--   The Finite Path construction uses the Hamming Weight single le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/FinitePath.lean#L166-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/FinitePath.lean#L166-L178

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
omit [Fintype F]

theorem QEC.Coding.FinitePath.HammingWeight_single_le_one
    {Index : Type*} [Fintype Index] [DecidableEq Index] (i : Index) :
    HammingWeight (Pi.single i (1 : F) : Word F Index) ≤ 1 := by sorry
