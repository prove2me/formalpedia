-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_lemmaD_8
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.lemmaD_8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:15:27.627884+00:00
-- url     : https://prove2.me/theorems/c57d1549-5678-472a-8077-f20f4685b21c
-- title:
--   Two-sided bounds on the sequential sparse-ensemble parameter
-- statement:
--   Let $n\ge1$ and let $S=\{(A,B):A\ne I^n,\ B\ne I^n\}$, containing every indicated positive Pauli exactly once. Include each paired negative. There are $2(4^n-1)^2$ signed observables and they satisfy all five conditions of Lemma D.6.
--
--   For any finite ancilla, a joint ancilla-input density matrix $\rho$, and a unit vector $\psi$ on ancilla-output, put $D=\langle\psi|(\rho_{\rm aux}\otimes I)|\psi\rangle$. On branches with $D>0$, let
--
--   $$X_{A,B}=\operatorname{tr}_{\rm in}\!\left[(\rho^{T_{\rm in}}\otimes I)(I_{\rm aux}\otimes P_A\otimes P_B)\right],\qquad
--   \Delta(S)=\sup\frac1{|S|}\sum_{(A,B)\in S}\left(\frac{\langle\psi|X_{A,B}|\psi\rangle}{D}\right)^2.$$
--
--   The supremum ranges over all such finite ancillas, states, unit vectors and positive-denominator branches. Its value set is nonempty and bounded, and
--
--   $$\frac1{(2^n+1)^2}\le\Delta(S)\le\frac1{(2^n-1)^2}.$$
--
--   Both inequalities are retained; no equality is asserted.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 52, Lemma D.8

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.52-57, Lemma D.8. Both inequalities are retained, and the
likelihood supremum ranges over all finite ancillas and positive baseline branches. -/
theorem lemmaD_8 (n : ℕ) (hn : 1 ≤ n) :
    (sparseEnsemble n).card = (4^n - 1)^2 ∧
    sparseEnsembleValid (sparseEnsemble n) ∧
    (likelihoodValues (sparseEnsemble n)).Nonempty ∧
    BddAbove (likelihoodValues (sparseEnsemble n)) ∧
    (((2 : ℝ)^n + 1)^2)⁻¹ ≤ likelihoodParameter (sparseEnsemble n) ∧
    likelihoodParameter (sparseEnsemble n) ≤ (((2 : ℝ)^n - 1)^2)⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
