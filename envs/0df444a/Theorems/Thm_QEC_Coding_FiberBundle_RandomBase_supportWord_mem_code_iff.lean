-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_iff
-- name    : QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:39:46.319219+00:00
-- url     : https://prove2.me/theorems/be1c397c-5879-46e5-9e47-a69101e4e27a
-- title:
--   Random Base: support Word mem code iff
-- statement:
--   Passing all parity checks is the all-row parity-zero event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L278-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L278-L310

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_iff
    {r : Nat} (sample : Sample r)
    (A : Finset (Fin (4 * r))) :
    supportWord A ∈ (code sample).carrier ↔
      ∀ a : Fin (3 * r),
        RowParityZero A (sampleEquivRows r sample a) := by sorry
