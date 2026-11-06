-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_horizontalAugmentation_ne_zero_of_homologyProjection_ne_zero
-- name    : QEC.Coding.BalancedProduct.HorizontalSubsystem.horizontalAugmentation_ne_zero_of_homologyProjection_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:10:57.503614+00:00
-- url     : https://prove2.me/theorems/362816d3-7e07-4186-8e6a-fbef5421015e
-- title:
--   Horizontal Subsystem: horizontal Augmentation ne zero of homology Projection ne zero
-- statement:
--   A source middle cycle whose horizontal homology projection is nonzero has
--   a nonzero horizontal augmentation.  This follows from the actual induced
--   homology map; no distance conclusion is stored in the subsystem data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L459-L481
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L459-L481

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.HorizontalSubsystem.horizontalAugmentation_ne_zero_of_homologyProjection_ne_zero
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A x)).middleCycleCode.carrier)
    (hProjected : horizontalHomologyProjection A x
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A x)).middleBoundaryInCycles.mkQ
          ⟨z, hz⟩) ≠ 0) :
    horizontalAugmentation z ≠ 0 := by sorry
