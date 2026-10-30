-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_lemmaD_4
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.lemmaD_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:14:45.029054+00:00
-- url     : https://prove2.me/theorems/4f8a4ef8-f761-4631-b7c3-82d4dc7e7661
-- title:
--   The doubly-stochastic sparse ensemble and its shadow parameter
-- statement:
--   Let $n\ge1$. On a reference/input register and an output register of $n$ qubits each, $P_A\otimes P_B$ denotes the ordinary unnormalized Pauli product. Enumerations below contain every indicated positive Pauli exactly once and its paired negative. For their positive-label set $S$, define
--
--   $$\delta(S)=\sup_{\|\psi\|=1}\frac{1}{|S|}\sum_{(A,B)\in S}\langle\psi|P_A\otimes P_B|\psi\rangle^2.$$
--
--   The unit-vector domain is nonempty and the displayed value set is bounded above, so the real supremum has its usual meaning.
--
--   Take $S=\{(A,B):A\ne I^n,\ B\ne I^n\}$. Then
--
--   $$|S|=(4^n-1)^2,\qquad\delta(S)=\frac1{4^n-1}.$$
--
--   All signed observables are Hermitian traceless involutions, with both input and output partial traces zero and canonically paired negatives. Each is a tensor product of $2n$ single-qubit observables and a single Pauli string, hence one-sparse. Thus the enumeration satisfies all five conditions of Lemma D.2.
--
--   This is the ensemble for sparse unital channel lower bounds.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 45, Lemma D.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.45-46, Lemma D.4. All observables are explicit single Pauli
products, hence one-sparse; both marginal constraints are conclusions. -/
theorem lemmaD_4 (n : ℕ) (hn : 1 ≤ n) :
    (sparseEnsemble n).card = (4^n - 1)^2 ∧
    sparseEnsembleValid (sparseEnsemble n) ∧
    (shadowValues (sparseEnsemble n)).Nonempty ∧
    BddAbove (shadowValues (sparseEnsemble n)) ∧
    shadowParameter (sparseEnsemble n) = ((4 : ℝ)^n - 1)⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
