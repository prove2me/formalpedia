-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_add_subword_add_hammingWeight
-- name    : QEC.Coding.FiberBundle.hammingWeight_add_subword_add_hammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:46:50.716323+00:00
-- url     : https://prove2.me/theorems/8e9cc0b6-662e-4e8c-860b-8d656f476cca
-- title:
--   Fiber Bundle: hamming Weight add subword add hamming Weight
-- statement:
--   Deleting a binary subword partitions Hamming weight exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1387-L1414
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1387-L1414

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_add_subword_add_hammingWeight
    {ι : Type u} [Fintype ι]
    (h z : Word (ZMod 2) ι)
    (hhz : IsBinarySubword h z) :
    HammingWeight (z + h) + HammingWeight h =
      HammingWeight z := by sorry
