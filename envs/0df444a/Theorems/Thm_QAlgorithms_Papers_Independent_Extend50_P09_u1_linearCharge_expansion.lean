-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_linearCharge_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_linearCharge_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:41:36.125058+00:00
-- url     : https://prove2.me/theorems/2ced251c-e0c8-4f88-a17a-359eb3bd075e
-- title:
--   Appendix C1: linear-charge fidelity and purified-distance expansion
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   All logarithms are base two. Asymptotic inequalities are eventual bounds with positive constants chosen before the sizes, ancillary vectors, and erased sets over which they are uniform. For fixed $0<a<1$, $\alpha=an$ is imposed only along an admissible unbounded integer-size subsequence, with positive $k,t$; the threshold may depend on its little-o convergence rate.
--
--   Let $F_n=F(\Omega_{RE},I_R/2^k\otimes\zeta_0)$ and $P_n=P(\Omega_{RE},I_R/2^k\otimes\zeta_0)$, where $\Omega$ and its environmental marginal $\zeta_0$ are the exact averaged Choi objects of Appendix C1. If $kt=o(n)$ then
--   $$F_n=1-\frac{tk}{32a(1-a)n^2}+O(k^3t^3/n^3).$$
--   If additionally $k^2t^2=o(n)$, then
--   $$P_n=\frac{\sqrt{tk}}{4n\sqrt{a(1-a)}}\left(1+O(k^2t^2/n)\right).$$
--
--   The errors are absolute for the fidelity expansion and relative for purified distance, with constants depending only on the fixed $a$.
--
--   The preceding (C14) expansion is retained uniformly over $0\le j\le k$ under $kt=o(n)$, with the same parameter-independent remainder constant:
--   $$\sum_{i=0}^t\binom ti\sqrt{\beta_i h_{j,i}}=1-\frac{t(k-2j)^2}{32a(1-a)n^2}+O(k^3t^3/n^3).$$
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 20, Appendix C1: linear-charge fidelity and purified-distance expansion

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

/-- Appendix C1, PDF p.20, (C14)–(C16), including C14 uniformly for
all logical weights 0<=j<=k. Fidelity expansion holds under
kt=o(n); the relative purified-distance expansion uses k²t²=o(n).
Constants precede all admissible subsequences. -/
theorem u1_linearCharge_expansion (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N k t alpha : ℕ → ℕ,
    Tendsto N atTop atTop →
    (∀ i, 0 < N i ∧ 0 < k i ∧ k i ≤ N i ∧ 0 < t i ∧ t i ≤ N i ∧
      alpha i ≤ N i-k i ∧ (alpha i : ℝ) = a*N i) →
    (Tendsto (fun i => (k i : ℝ)*t i/N i) atTop (nhds 0) →
      ∃ i0 : ℕ, ∀ i ≥ i0,
      (∀ j : ℕ, j ≤ k i →
        |(∑ r ∈ Finset.range (t i+1), ((t i).choose r : ℝ) *
          Real.sqrt (choiMarginalCoefficient (N i) (k i) (t i) (alpha i) r *
            hyper (N i) (t i) (j+alpha i) r)) -
          (1-(t i : ℝ)*((k i : ℝ)-2*j)^2/(32*a*(1-a)*(N i : ℝ)^2))| ≤
            C*(k i : ℝ)^3*(t i : ℝ)^3/(N i : ℝ)^3) ∧
      |comparatorFidelity (N i) (k i) (t i) (alpha i) -
        (1-(t i : ℝ)*k i/(32*a*(1-a)*(N i : ℝ)^2))| ≤
          C*(k i : ℝ)^3*(t i : ℝ)^3/(N i : ℝ)^3) ∧
    (Tendsto (fun i => u1Ratio false (N i) (k i) (t i)) atTop (nhds 0) →
      ∃ i0 : ℕ, ∀ i ≥ i0,
      |comparatorDistance (N i) (k i) (t i) (alpha i) /
        u1Leading false a (N i) (k i) (t i)-1| ≤
          C*u1Ratio false (N i) (k i) (t i)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
