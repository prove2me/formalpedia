-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_basis_twirl_and_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_basis_twirl_and_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:43:17.476515+00:00
-- url     : https://prove2.me/theorems/cc0bdd2d-fd8c-40ed-91d1-3a15bf4ec9d6
-- title:
--   Appendix C2: basis averages and maximal symmetry term
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   All logarithms are base two. Asymptotic inequalities are eventual bounds with positive constants chosen before the sizes, ancillary vectors, and erased sets over which they are uniform. For fixed $0<a<1$, $\alpha=an$ is imposed only along an admissible unbounded integer-size subsequence, with positive $k,t$; the threshold may depend on its little-o convergence rate.
--
--   For all distinct computational words $x,y$, and with $q=|x|+\alpha$,
--   $$\mathbb E_U\mathcal E_U(|x\rangle\langle y|)=0,\qquad
--   \mathbb E_U\mathcal E_U(|x\rangle\langle x|)=\Pi_q^{(n)}/\binom nq.$$
--   Let $\rho_{\rm avg}^{x,x}$ be its $t$-site marginal and $\zeta_0$ the uniform average of these marginals. In the interior linear-charge regime $kt^2=o(n)$,
--   $$\max_xP(\rho_{\rm avg}^{x,x},\zeta_0)=\frac{k\sqrt t}{4n\sqrt{a(1-a)}}\left(1+O(kt^2/n)\right).$$
--
--   The twirl is exact without asymptotic restrictions. The displayed expansion restores the missing O in printed (C23), as supported by (C14) and Theorem 3.
--
--   The exact environmental average and its fidelity are also retained: with $q=|x|+\alpha$,
--   $$\rho_{\rm avg}^{x,x}=\sum_{i=0}^t h(q,i)\Pi_i^{(t)},\qquad F(\rho_{\rm avg}^{x,x},\zeta_0)=\sum_{i=0}^t\binom ti\sqrt{\beta_i h(q,i)},$$
--   where $h(q,i)=\binom{n-t}{q-i}/\binom nq$ with signed invalid binomial indices zero, and $\beta_i$ is the uniform logical-basis marginal coefficient defined above.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 21, Appendix C2: basis averages and maximal symmetry term

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Appendix C2, PDF p.21, (C19)–(C23): exact basis twirl and maximal
symmetry distance. The missing O in printed (C23) is restored using (C14)
and Theorem 3; no exact finite-n equality is asserted for that expansion. -/
theorem u1_basis_twirl_and_expansion :
    (∀ n k alpha : ℕ, ∀ hk : k ≤ n, alpha ≤ n-k →
      ∀ psi : EuclideanSpace ℂ (CovariantWord 2 (n-k)), ChargeState alpha psi →
      ∀ mu : Measure (Op (CovariantWord 2 n)), IsCommutantHaarLaw (U1Group n) mu →
      ∀ x y : CovariantWord 2 k,
      (∫ U, appendUnitaryEncoder hk (pureDensity psi) U (Matrix.single x y 1) ∂mu) =
        if x = y then (n.choose (chargeHammingWeight x+alpha) : ℂ)⁻¹ • u1SectorProjector n (chargeHammingWeight x+alpha) else 0) ∧
    (∀ n k t alpha : ℕ, ∀ hk : k ≤ n, ∀ ht : t ≤ n, alpha ≤ n-k →
      ∀ psi : EuclideanSpace ℂ (CovariantWord 2 (n-k)), ChargeState alpha psi →
      ∀ mu : Measure (Op (CovariantWord 2 n)), IsCommutantHaarLaw (U1Group n) mu →
      ∀ x : CovariantWord 2 k,
      firstTrace ht (∫ U, appendUnitaryEncoder hk (pureDensity psi) U (pureDensity (ket x)) ∂mu) =
        avgBasis n t (chargeHammingWeight x+alpha) ∧
      rootFidelity (avgBasis n t (chargeHammingWeight x+alpha)) (choiMarginalState n k t alpha) =
        ∑ i ∈ Finset.range (t+1), (t.choose i : ℝ) *
          Real.sqrt (choiMarginalCoefficient n k t alpha i *
            hyper n t (chargeHammingWeight x+alpha) i)) ∧
    (∀ a : ℝ, 0 < a → a < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ N k t alpha : ℕ → ℕ, Tendsto N atTop atTop →
      Tendsto (fun i => u1Ratio true (N i) (k i) (t i)) atTop (nhds 0) →
      (∀ i, 0 < N i ∧ 0 < k i ∧ k i ≤ N i ∧ 0 < t i ∧ t i ≤ N i ∧
        alpha i ≤ N i-k i ∧ (alpha i : ℝ) = a*N i) →
      ∃ i0 : ℕ, ∀ i ≥ i0,
      |basisDistance (N i) (k i) (t i) (alpha i) /
        u1Leading true a (N i) (k i) (t i)-1| ≤
          C*u1Ratio true (N i) (k i) (t i)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
