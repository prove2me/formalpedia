-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_average_choi
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_average_choi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:40:47.880372+00:00
-- url     : https://prove2.me/theorems/c0b3239b-09a6-40d1-b58e-9f8989b4d0e9
-- title:
--   Appendix C1: exact averaged Choi state, marginal and fidelity
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   For the normalized Choi input write $\Phi_{\rm avg}=\mathbb E_U(\mathrm{id}_R\otimes\mathcal E_U)(\Phi_k)$, and let $E$ be the first $t$ physical sites. Denote weight projectors by $\Pi_q^{(m)}$, with invalid sectors zero. Then
--   $$\Phi_{\rm avg}=2^{-k}\sum_{j=0}^k\Pi_j^{(k)}\otimes\frac{\Pi_{j+\alpha}^{(n)}}{\binom n{j+\alpha}},\qquad
--   \Omega_{RE}=\operatorname{Tr}_{n-t}\Phi_{\rm avg}=2^{-k}\sum_{j=0}^k\sum_{i=0}^t\frac{\binom{n-t}{j+\alpha-i}}{\binom n{j+\alpha}}\Pi_j^{(k)}\otimes\Pi_i^{(t)}.$$
--   Put $h_{j,i}=\binom{n-t}{j+\alpha-i}/\binom n{j+\alpha}$ and $\beta_i=2^{-k}\sum_j\binom kj h_{j,i}$. Its marginal is $\zeta_0=\operatorname{Tr}_R\Omega=\sum_i\beta_i\Pi_i^{(t)}$, and
--   $$F(\Omega,I_R/2^k\otimes\zeta_0)=2^{-k}\sum_{j=0}^k\sum_{i=0}^t\binom kj\binom ti\sqrt{\beta_i h_{j,i}}.$$
--
--   These identities specify the exact comparator used by the subsequent expansions, including signed binomial indices.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 19, Appendix C1: exact averaged Choi state, marginal and fidelity

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

/-- Appendix C1, PDF p.19, (C1)–(C6): exact joint average, environmental
marginal, choiMarginalState marginal and scalar root-fidelity expression. Every binomial
with negative lower index is zero, rather than Nat subtraction at zero. -/
theorem u1_average_choi (n k t alpha : ℕ) (hk : k ≤ n) (ht : t ≤ n)
    (ha : alpha ≤ n-k) (psi : EuclideanSpace ℂ (CovariantWord 2 (n-k)))
    (hpsi : ChargeState alpha psi) (mu : Measure (Op (CovariantWord 2 n)))
    (hmu : IsCommutantHaarLaw (U1Group n) mu) :
    (∫ U, idTensorSuperop (R := CovariantWord 2 k) (appendUnitaryEncoder hk (pureDensity psi) U)
      (pureDensity (bell (CovariantWord 2 k))) ∂mu) = avgFullChoi n k alpha ∧
    idTensorSuperop (R := CovariantWord 2 k) (firstTrace ht) (avgFullChoi n k alpha) =
      avgChoi n k t alpha ∧
    traceLeft (avgChoi n k t alpha) = choiMarginalState n k t alpha ∧
    comparatorFidelity n k t alpha =
      (2 : ℝ)^(- (k : ℤ)) * ∑ j ∈ Finset.range (k+1), ∑ i ∈ Finset.range (t+1),
        (k.choose j : ℝ)*(t.choose i : ℝ)*
          Real.sqrt (choiMarginalCoefficient n k t alpha i * hyper n t (j+alpha) i) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
