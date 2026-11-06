-- Prove2me | Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_middleHomologyDistanceAtLeast_of_forward_lipschitz
-- name    : QEC.Coding.ThreeTermChainHomotopyEquiv.middleHomologyDistanceAtLeast_of_forward_lipschitz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:34:03.062918+00:00
-- url     : https://prove2.me/theorems/2f8a2b5a-0709-4922-a47b-a08f62b7e460
-- title:
--   Three Term Chain Homotopy Equiv: middle Homology Distance At Least of forward lipschitz
-- statement:
--   An `L`-Lipschitz forward middle map transports a target homological
--   distance lower bound `d` to the source lower bound `d / L`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/HomotopyDistance.lean#L79-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/HomotopyDistance.lean#L79-L95

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

theorem QEC.Coding.ThreeTermChainHomotopyEquiv.middleHomologyDistanceAtLeast_of_forward_lipschitz
    (e : ThreeTermChainHomotopyEquiv A B)
    {d L : Nat}
    (hTarget : MiddleHomologyDistanceAtLeast B d)
    (hLipschitz : ∀ z : Word F ι1,
      HammingWeight (e.forward.map1 z) ≤ L * HammingWeight z) :
    MiddleHomologyDistanceAtLeast A (d / L) := by sorry
