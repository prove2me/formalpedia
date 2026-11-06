-- Prove2me | Theorems.Thm_QEC_Coding_HammingWeight_linearMap_le_of_basis
-- name    : QEC.Coding.HammingWeight_linearMap_le_of_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:41.578625+00:00
-- url     : https://prove2.me/theorems/db221ba5-f6e5-43e8-a8e3-0a05772c290d
-- title:
--   Coding: Hamming Weight linear Map le of basis
-- statement:
--   A linear map whose images of coordinate basis vectors have weight at
--   most `L` is `L`-Lipschitz for Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L69-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L69-L99

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
set_option autoImplicit false
open QEC QEC.Coding
open scoped BigOperators
universe u v w

theorem QEC.Coding.HammingWeight_linearMap_le_of_basis
    {F : Type u} [Field F] [DecidableEq F]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {κ : Type w} [Fintype κ]
    (f : Word F ι →ₗ[F] Word F κ) (L : Nat)
    (hBasis : ∀ i : ι, HammingWeight (f (Pi.single i 1)) ≤ L)
    (x : Word F ι) :
    HammingWeight (f x) ≤ L * HammingWeight x := by sorry
