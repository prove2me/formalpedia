-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_le_rightMarginal_add_sum_log_selectedDimensions
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_le_rightMarginal_add_sum_log_selectedDimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:48.00621+00:00
-- url     : https://prove2.me/theorems/b7d31c21-d5c9-4e2a-804d-c62930556b06
-- title:
--   Density Operator: von Neumann Entropy le right Marginal add sum log selected Dimensions
-- statement:
--   BPT-ready entropy composition with the concrete heterogeneous qudit dimension bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L748-L756
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L748-L756

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_le_rightMarginal_add_sum_log_selectedDimensions
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι -> Nat} (S : QuditSubsystem q)
    (rho : DensityOperator (CompositeSystem H S.selectedSystem)) :
    rho.vonNeumannEntropy <= (rightMarginal rho).vonNeumannEntropy +
      ∑ i ∈ S.selected, Real.logb 2 (q i : Real) := by sorry
