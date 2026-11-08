-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_tradeoff_blockLength_le
-- name    : QEC.Coding.ExpanderCodes.PK20.tradeoff_blockLength_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:38:21.308657+00:00
-- url     : https://prove2.me/theorems/63ea3f92-5a31-4375-8d1b-a1d859244e88
-- title:
--   PK20: tradeoff block Length le
-- statement:
--   The actual final blocklength is at most four times the initial blocklength
--   times the square of the number of classical bits.  This is the finite
--   inequality used in PK20's exponent calculation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/Tradeoff.lean#L103-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/Tradeoff.lean#L103-L157

import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
import Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.tradeoff_blockLength_le
    (q n m r nc mc w : Nat) [NeZero q] [NeZero r]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (C : Matrix (Fin mc) (Fin (w * nc))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r)))
    (hChecks : mc ≤ w * nc) :
    Fintype.card
        (SecondQubit
          (xZero := InitialC0 q n m w)
          (xOne := InitialQubit q n m w)
          (xTwo := InitialC2 q n m w)
          (bitOne := FactorBit r nc w)
          (checkOne := FactorCheck r nc mc w C)
          (bitTwo := FactorBit r nc w)
          (checkTwo := FactorCheck r nc mc w C)) ≤
      4 * blockLength q A * Fintype.card (FactorBit r nc w) ^ 2 := by sorry
