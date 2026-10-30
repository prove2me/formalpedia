-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_entropy_estimates
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_entropy_estimates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:35:27.658686+00:00
-- url     : https://prove2.me/theorems/b8826784-c304-4d37-8e8c-c9008dd9f2bf
-- title:
--   Appendix A1: U(1) entropy bounds
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   For finite positive-dimensional registers $P,Q$ and a positive operator $X^{PQ}$, write $H_{\min}(P|Q)_X=\sup\{h:\exists\sigma_Q\ge0,\ \operatorname{Tr}\sigma_Q=1,\ X\le2^{-h}I_P\otimes\sigma_Q\}$. The supremum is extended-real, so $H_{\min}(0)=+\infty$; throughout, $-\log_2 0=+\infty$.
--
--   Construct the U(1) $\Lambda$ from (B3)–(B4), using the initial normalized Choi state or a logical computational basis state or one of the four normalized superpositions of two distinct basis words, with the same ancilla. Put $h=\min\{H_b(\alpha/n),H_b((\alpha+k)/n)\}$. There are absolute $C>0,n_0$ such that for all admissible positive $n\ge n_0$,
--   $$H_{\min}^{\rm Choi}\ge nh-(2t+k)-C\log_2 n,\qquad
--   H_{\min}^{\rm basis/superposition}\ge nh-2t-C\log_2 n.$$
--
--   The latter inputs have trivial reference. The estimate uses the constructed operators and does not rely on the deferred exact superposition sandwich (B35).
--
--   Before the asymptotic estimates the exact finite bounds hold with
--   $$M=\max\{\binom n\alpha^{-1},\binom n{\alpha+k}^{-1}\}:\qquad H_{\min}^{\rm Choi}\ge-(2t+k)-\log_2M,\qquad H_{\min}^{\rm basis/superposition}\ge-2t-\log_2M.$$
--   These are the supported-sector maximum in (A13)–(A14), using binomial unimodality, and include zero-size boundary cases.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 16, Appendix A1: U(1) entropy bounds

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

/-- Appendix A1, PDF p.16, (A13)–(A14), with explicit eventual
O(log n), preceded by the exact finite bound with the largest inverse
binomial coefficient in the supported charge interval. Basis inputs and the
four normalized superpositions are included. -/
theorem u1_entropy_estimates :
    (∀ n k t alpha : ℕ, ∀ hk : k ≤ n, ∀ ht : t ≤ n, alpha ≤ n-k →
      ∀ psi : EuclideanSpace ℂ (CovariantWord 2 (n-k)), ChargeState alpha psi →
      let M := max ((n.choose alpha : ℝ)⁻¹) ((n.choose (alpha+k) : ℝ)⁻¹)
      ((-(2*(t : ℝ)+k) : ℝ) : EReal) + negLog M ≤
        conditionalMinEntropy (choiLambda hk ht psi) ∧
      (∀ x : CovariantWord 2 k,
        ((-2*(t : ℝ) : ℝ) : EReal) + negLog M ≤
          conditionalMinEntropy (simpleLambda hk ht psi (ket x))) ∧
      (∀ x y : CovariantWord 2 k, x ≠ y → ∀ z : ℂ, FourPhase z →
        ((-2*(t : ℝ) : ℝ) : EReal) + negLog M ≤
          conditionalMinEntropy (simpleLambda hk ht psi (superposition x y z)))) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ k t alpha : ℕ,
    ∀ hk : k ≤ n, ∀ ht : t ≤ n, 0 < n → alpha ≤ n-k →
    ∀ psi : EuclideanSpace ℂ (CovariantWord 2 (n-k)), ChargeState alpha psi →
    let H := min (binEntropy2 ((alpha : ℝ)/n)) (binEntropy2 (((alpha+k : ℕ) : ℝ)/n))
    (((n : ℝ)*H - (2*(t : ℝ)+k) - C*Real.logb 2 n : ℝ) : EReal) ≤ conditionalMinEntropy (choiLambda hk ht psi) ∧
    (∀ x : CovariantWord 2 k, (((n : ℝ)*H-2*t-C*Real.logb 2 n : ℝ) : EReal) ≤
      conditionalMinEntropy (simpleLambda hk ht psi (ket x))) ∧
    (∀ x y : CovariantWord 2 k, x ≠ y → ∀ z : ℂ, FourPhase z →
      (((n : ℝ)*H-2*t-C*Real.logb 2 n : ℝ) : EReal) ≤
        conditionalMinEntropy (simpleLambda hk ht psi (superposition x y z))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
