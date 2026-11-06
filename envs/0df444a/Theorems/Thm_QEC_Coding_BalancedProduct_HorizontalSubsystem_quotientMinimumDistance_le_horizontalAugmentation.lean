-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_quotientMinimumDistance_le_horizontalAugmentation
-- name    : QEC.Coding.BalancedProduct.HorizontalSubsystem.quotientMinimumDistance_le_horizontalAugmentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:37:21.641033+00:00
-- url     : https://prove2.me/theorems/11797b15-2572-4b02-9d81-639de1c8b83c
-- title:
--   Horizontal Subsystem: quotient Minimum Distance le horizontal Augmentation
-- statement:
--   A nonzero selected horizontal class inherits the minimum-distance lower
--   bound of the concrete quotient Tanner cycle code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L515-L537
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L515-L537

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.HorizontalSubsystem.quotientMinimumDistance_le_horizontalAugmentation
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A x)).middleCycleCode.carrier)
    {d : Nat}
    (hMinimum : MinimumDistance
      (quotientTannerComplex A).middleCycleCode d)
    (hProjected : horizontalHomologyProjection A x
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A x)).middleBoundaryInCycles.mkQ
          ⟨z, hz⟩) ≠ 0) :
    d ≤ HammingWeight (horizontalAugmentation z) := by sorry
