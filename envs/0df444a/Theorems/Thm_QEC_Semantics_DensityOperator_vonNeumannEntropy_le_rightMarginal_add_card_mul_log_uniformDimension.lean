-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_le_rightMarginal_add_card_mul_log_uniformDimension
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_le_rightMarginal_add_card_mul_log_uniformDimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:53:40.19554+00:00
-- url     : https://prove2.me/theorems/97b777cf-39ae-4415-bada-1bedbb10da51
-- title:
--   Density Operator: von Neumann Entropy le right Marginal add card mul log uniform Dimension
-- statement:
--   BPT-ready uniform-dimension corollary, available only under an explicit local bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L759-L769
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L759-L769

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_le_rightMarginal_add_card_mul_log_uniformDimension
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι -> Nat} (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) (D : Nat)
    (hD : ∀ i, i ∈ S.selected -> q i <= D)
    (rho : DensityOperator (CompositeSystem H S.selectedSystem)) :
    rho.vonNeumannEntropy <= (rightMarginal rho).vonNeumannEntropy +
      (S.selected.card : Real) * Real.logb 2 (D : Real) := by sorry
