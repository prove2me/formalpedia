-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_lowWeightSupport_mem_code_of_not_hasLinearDistance
-- name    : QEC.Coding.FiberBundle.RandomBase.exists_lowWeightSupport_mem_code_of_not_hasLinearDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:44:28.996073+00:00
-- url     : https://prove2.me/theorems/1cbc180f-db41-4051-b231-29046e436462
-- title:
--   Random Base: exists low Weight Support mem code of not has Linear Distance
-- statement:
--   A failed linear-distance event supplies a concrete low-weight support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L810-L832
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L810-L832

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.exists_lowWeightSupport_mem_code_of_not_hasLinearDistance
    {r : Nat} {sample : Sample r}
    (h : ¬HasLinearDistance sample) :
    ∃ A : LowWeightSupport r,
      supportWord A.1 ∈ (code sample).carrier := by sorry
