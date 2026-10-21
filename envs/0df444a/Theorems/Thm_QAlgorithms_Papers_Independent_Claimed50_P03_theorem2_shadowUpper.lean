-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_theorem2_shadowUpper
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.theorem2_shadowUpper
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:41:27.55227+00:00
-- url     : https://prove2.me/theorems/89310104-dd73-47d8-aba3-0d829e895b77
-- title:
--   Theorem 2 (Sample complexity upper bound)
-- statement:
--   A randomized Pauli shot chooses each wire's axis uniformly from $X,Y,Z$ and then records its Born-distributed eigenvalue. Its inverse snapshot is $\widehat\rho=\bigotimes_i(3|s_i\rangle\langle s_i|-I)$. Shots are independent. The uncentered shadow norm is $\|O\|_{\rm sh}=\sup_{\sigma\text{ density}}(\mathbb E_\sigma[\operatorname{tr}(O\widehat\rho)^2])^{1/2}$.
--
--   For integers $k,d\ge1$, set
--   $$C(k,d)=\frac{\sqrt{2k!}}{\sqrt d\,k^{k+5/2}(2\sqrt6+4\sqrt3)^k}.$$
--   A bounded-degree decomposition means a finite sum of Hermitian terms supported on at most $k$ wires each, with at most $d$ terms incident on any wire.
--
--   Let $n,M\ge1$, $B,\epsilon>0$, and let the Hermitian observables $O_1,\ldots,O_M$ all have such a decomposition and satisfy $\|O_i\|\le B$. Define $h_N(O)=N^{-1}\sum_{\ell=1}^N\operatorname{tr}(O\widehat\rho_\ell)$ and $A(k,d)=(k+1)3^{2k}(3/C(k,d))^2$. There is a universal $K>0$, independent of all these parameters, such that taking
--   $$N\ge\max\!\left\{1,\left\lceil K A(k,d)\frac{B^2}{\epsilon^2}\,[1+\log\min(M,n)]\right\rceil\right\}$$
--   ensures, for every unknown density matrix $\rho$,
--   $$\Pr\{\forall i:\ |h_N(O_i)-\operatorname{tr}(O_i\rho)|\le\epsilon\}\ge\frac34.$$
--   For fixed locality and degree this is $O(B^2\epsilon^{-2}\log\min(M,n))$, with positive rounding at the boundary. The precise sufficient locality factor is $k^{O(k)}$, and its dependence on $d$ is polynomial. The two source routes compute the same linear empirical predictor, either through target snapshots or through common low-weight Pauli coefficients.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 8, Theorem 2 (Sample complexity upper bound)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Theorem 2, paper p.8, Eq.25. Actual empirical predictor; a universal
constant precedes locality, degree, n, M, state and observable family. Rounding
and 1+log protect min(M,n)=1; the constant success probability is 3/4. -/
theorem theorem2_shadowUpper :
    ∃ C : ℝ, 0 < C ∧ ∀ (k d n M N : ℕ), 1 ≤ k → 1 ≤ d → 1 ≤ n → 1 ≤ M →
      ∀ (eps B : ℝ), 0 < eps → 0 < B →
      ∀ O : Fin M → (Matrix (Qubits n) (Qubits n) ℂ),
      (∀ i, (O i).IsHermitian ∧ HasBoundedDegree k d (O i) ∧ specNorm (O i) ≤ B) →
      ∀ rho : (Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho →
      max 1 ⌈C * shadowSampleScale k d * B ^ 2 / eps ^ 2 *
        (1 + Real.log (min M n : ℕ))⌉₊ ≤ N →
      3 / 4 ≤ shotEventProbability (N := N) rho
        (fun data => ∀ i, |shadowPredictor data (O i) - effectProb (O i) rho| ≤ eps) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
