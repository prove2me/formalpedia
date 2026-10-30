-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_lemmaD_3
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.lemmaD_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:13:44.952687+00:00
-- url     : https://prove2.me/theorems/6c0bb1f6-9f04-49c9-b86f-933d9e018489
-- title:
--   The Choi Pauli ensemble and its shadow parameter
-- statement:
--   Let $n\ge1$. On a reference/input register and an output register of $n$ qubits each, $P_A\otimes P_B$ denotes the ordinary unnormalized Pauli product. Enumerations below contain every indicated positive Pauli exactly once and its paired negative. For their positive-label set $S$, define
--
--   $$\delta(S)=\sup_{\|\psi\|=1}\frac{1}{|S|}\sum_{(A,B)\in S}\langle\psi|P_A\otimes P_B|\psi\rangle^2.$$
--
--   The unit-vector domain is nonempty and the displayed value set is bounded above, so the real supremum has its usual meaning.
--
--   Take $S=\{(A,B):B\ne I^n\}$. Then
--
--   $$|S|=4^n(4^n-1),\qquad\delta(S)=4^{-n}.$$
--
--   Each of the $2|S|$ signed observables is Hermitian, traceless, squares to the identity, and has zero output partial trace. Its paired observable is its negative. These are exactly conditions (i)–(iii) of Lemma D.1.
--
--   This evaluates the ensemble parameter used in the memoryless Choi lower bound.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 44, Lemma D.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.44-45, Lemma D.3. Both signs of every indicated distinct Pauli
occur, with negative half paired canonically. The supremum domain is guarded. -/
theorem lemmaD_3 (n : ℕ) (hn : 1 ≤ n) :
    (fullEnsemble n).card = 4^n * (4^n - 1) ∧
    choiEnsembleValid (fullEnsemble n) ∧
    (shadowValues (fullEnsemble n)).Nonempty ∧
    BddAbove (shadowValues (fullEnsemble n)) ∧
    shadowParameter (fullEnsemble n) = ((4 : ℝ)^n)⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
