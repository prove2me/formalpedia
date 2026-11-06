-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_subadditive_bipartite
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_subadditive_bipartite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:44:26.795511+00:00
-- url     : https://prove2.me/theorems/3dd52107-3784-47e8-b0f1-cdd18593378e
-- title:
--   Density Operator: von Neumann Entropy subadditive bipartite
-- statement:
--   The Density Operator construction uses the von Neumann Entropy subadditive bipartite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L561-L745
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L561-L745

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
set_option maxHeartbeats 3000000

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_subadditive_bipartite
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] (rho : DensityOperator (CompositeSystem H K)) :
    rho.vonNeumannEntropy <=
      (rightMarginal rho).vonNeumannEntropy + (leftMarginal rho).vonNeumannEntropy := by sorry
