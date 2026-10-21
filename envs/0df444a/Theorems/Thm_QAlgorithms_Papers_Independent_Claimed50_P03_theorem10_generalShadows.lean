-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_theorem10_generalShadows
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.theorem10_generalShadows
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:54:07.619261+00:00
-- url     : https://prove2.me/theorems/2a0157c8-87c4-45db-a3ba-e7d8c6d1ba24
-- title:
--   Theorem 10 (Classical shadow tomography using randomized Pauli measurements [46])
-- statement:
--   A randomized Pauli shot chooses each wire's axis uniformly from $X,Y,Z$ and then records its Born-distributed eigenvalue. Its inverse snapshot is $\widehat\rho=\bigotimes_i(3|s_i\rangle\langle s_i|-I)$. Shots are independent. The uncentered shadow norm is $\|O\|_{\rm sh}=\sup_{\sigma\text{ density}}(\mathbb E_\sigma[\operatorname{tr}(O\widehat\rho)^2])^{1/2}$.
--
--   Let $n,M\ge1$, $\epsilon,B_{\rm sh}>0$, and let $O_1,\ldots,O_M$ be Hermitian with $\|O_i\|_{\rm sh}\le B_{\rm sh}$. A universal $K>0$ suffices: if
--   $$N\ge\max\{1,\lceil K B_{\rm sh}^2\epsilon^{-2}(1+\log M)\rceil\},$$
--   there is a predictor chosen from the observable family and accuracy parameters before the unknown state, such that for every normalized $\rho$,
--   $$\Pr\{\forall i:\ |h(S_N(\rho),i)-\operatorname{tr}(O_i\rho)|\le\epsilon\}\ge3/4.$$
--   The predictor may use median of means. This is the general shadow-norm sample guarantee, not a general assertion about an unmodified sample mean.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 32, Theorem 10 (Classical shadow tomography using randomized Pauli measurements [46])

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Theorem 10, paper p.32, C2; original arXiv:2002.08953, Supplementary
Theorem 1, S13-S14. The estimator is chosen before the unknown state and may
use median of means; no mean-only theorem for general observables is asserted. -/
theorem theorem10_generalShadows :
    ∃ C : ℝ, 0 < C ∧ ∀ (n M N : ℕ), 1 ≤ n → 1 ≤ M →
      ∀ (eps Bshadow : ℝ), 0 < eps → 0 < Bshadow →
      ∀ O : Fin M → (Matrix (Qubits n) (Qubits n) ℂ),
      (∀ i, (O i).IsHermitian ∧ localPauliShadowNorm (O i) ≤ Bshadow) →
      max 1 ⌈C * Bshadow ^ 2 / eps ^ 2 * (1 + Real.log (M : ℝ))⌉₊ ≤ N →
      ∃ predictor : (Fin N → Shot n) → Fin M → ℝ,
        ∀ rho : (Matrix (Qubits n) (Qubits n) ℂ), IsDensityMatrix rho →
          3 / 4 ≤ shotEventProbability (N := N) rho
            (fun data => ∀ i, |predictor data i - effectProb (O i) rho| ≤ eps) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
