-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_sum_prod_bool
-- name    : QuantumMaxCutEnergy.sum_prod_bool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:18:19.736784+00:00
-- url     : https://prove2.me/theorems/9ee2ff44-ad06-4dc7-807a-88bee7b3b0d0
-- title:
--   A sum of a product over a product equals a product of sums
-- statement:
--   For any commutative semiring $R$, any family $F_i : \{0,1\}\to R$ indexed by $i\in\{1,\dots,n\}$ satisfies
--   $$\sum_{x\in\{0,1\}^n}\ \prod_{i=1}^{n}F_i(x_i)\;=\;\prod_{i=1}^{n}\big(F_i(0)+F_i(1)\big).$$
--
--   This is distributivity read as a change of summation order: expanding the product on the right produces one term for each choice of $x_i\in\{0,1\}$, i.e. exactly the left-hand side. It follows from `Finset.prod_univ_sum`, which expresses a product of sums as a sum over the product of the index sets.
--
--   It is the workhorse behind both the norm computation for product states and the energy computation: the amplitude of a product state is by definition a product over the qubits, and summing over all computational basis vectors is a sum over $\{0,1\}^n$.
-- source:
--   Distributivity / Finset.prod_univ_sum; combinatorial identity for product states.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEnergy_prodState

open Complex
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Sum of a product over a product of index sets.** -/
theorem sum_prod_bool {n : ℕ} {R : Type*} [CommSemiring R] (F : Fin n → Bool → R) :
    (∑ x : Fin n → Bool, ∏ i, F i (x i))
      = ∏ i, (F i false + F i true) := by sorry

end QuantumMaxCutEnergy
