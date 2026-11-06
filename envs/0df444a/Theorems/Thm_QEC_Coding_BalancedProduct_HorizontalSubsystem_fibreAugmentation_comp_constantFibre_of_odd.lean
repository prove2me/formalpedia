-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_fibreAugmentation_comp_constantFibre_of_odd
-- name    : QEC.Coding.BalancedProduct.HorizontalSubsystem.fibreAugmentation_comp_constantFibre_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:37:36.224336+00:00
-- url     : https://prove2.me/theorems/b72fbb13-6325-4822-b58e-bfdac2b9d36d
-- title:
--   Horizontal Subsystem: fibre Augmentation comp constant Fibre of odd
-- statement:
--   The Horizontal Subsystem construction uses the fibre Augmentation comp constant Fibre of odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L372-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L372-L382

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.HorizontalSubsystem.fibreAugmentation_comp_constantFibre_of_odd
    {I G : Type} [Fintype G] (hOdd : Odd (Fintype.card G)) :
    (fibreAugmentation (I := I) (G := G)).comp constantFibre =
      LinearMap.id := by sorry
