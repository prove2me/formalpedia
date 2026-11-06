-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_horizontalAugmentation_eq_zero_of_homologyProjection_eq_zero
-- name    : QEC.Coding.BalancedProduct.HorizontalSubsystem.horizontalAugmentation_eq_zero_of_homologyProjection_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:37:44.880216+00:00
-- url     : https://prove2.me/theorems/43bdfcb0-acb6-41d7-8ade-82b6ad0dd273
-- title:
--   Horizontal Subsystem: horizontal Augmentation eq zero of homology Projection eq zero
-- statement:
--   Vanishing of the selected horizontal homology class forces the concrete
--   horizontal augmentation to vanish.  The target quotient Tanner complex has
--   zero degree-two boundary, so this is stronger than a merely homologous-to-zero
--   statement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L487-L511
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L487-L511

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.HorizontalSubsystem.horizontalAugmentation_eq_zero_of_homologyProjection_eq_zero
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
          ⟨z, hz⟩) = 0) :
    horizontalAugmentation z = 0 := by sorry
