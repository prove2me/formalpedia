-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
-- name    : QEC.Semantics.DensityOperator.convexCombination_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:14:14.063185+00:00
-- url     : https://prove2.me/theorems/fc905b59-a1e2-4101-92a6-a44dcf77af25
-- title:
--   Density Operator: convex Combination to Operator
-- statement:
--   The Density Operator construction uses the convex Combination to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Convexity.lean#L76-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Convexity.lean#L76-L81

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_Convexity
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open QEC.Semantics.DensityOperator
open scoped BigOperators ComplexOrder
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.convexCombination_toOperator {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    (convexCombination s w ρ hw_nonneg hw_sum).toOperator =
      convexCombinationOperator s w ρ := by sorry

attribute [defeq] QEC.Semantics.DensityOperator.convexCombination_toOperator
