-- Prove2me | Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_middleCohomologyDistanceAtLeast_of_inverse_transpose_lipschitz
-- name    : QEC.Coding.ThreeTermChainHomotopyEquiv.middleCohomologyDistanceAtLeast_of_inverse_transpose_lipschitz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:35:32.460314+00:00
-- url     : https://prove2.me/theorems/dece5c3b-348e-4384-9393-2597425d2930
-- title:
--   Three Term Chain Homotopy Equiv: middle Cohomology Distance At Least of inverse transpose lipschitz
-- statement:
--   An `L`-Lipschitz transpose of the inverse middle map transports a target
--   cohomological distance lower bound `d` to the source lower bound `d / L`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/HomotopyDistance.lean#L129-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/HomotopyDistance.lean#L129-L146

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
set_option autoImplicit false
open QEC QEC.Coding
universe u v w
open QEC.Coding.ThreeTermChainHomotopyEquiv
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
variable {κ0 κ1 κ2 : Type w} [Fintype κ0] [Fintype κ1] [Fintype κ2]
variable {A : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2)}
variable {B : ChainComplexData F (Word F κ0) (Word F κ1) (Word F κ2)}

theorem QEC.Coding.ThreeTermChainHomotopyEquiv.middleCohomologyDistanceAtLeast_of_inverse_transpose_lipschitz
    (e : ThreeTermChainHomotopyEquiv A B)
    {d L : Nat}
    (hTarget : MiddleCohomologyDistanceAtLeast B d)
    (hLipschitz : ∀ x : Word F ι1,
      HammingWeight (wordLinearMapTranspose e.inverse.map1 x) ≤
        L * HammingWeight x) :
    MiddleCohomologyDistanceAtLeast A (d / L) := by sorry
