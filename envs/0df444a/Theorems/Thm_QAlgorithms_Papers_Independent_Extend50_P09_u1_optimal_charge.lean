-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_optimal_charge
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_optimal_charge
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:25:32.330721+00:00
-- url     : https://prove2.me/theorems/e49b9d18-9441-49da-9e15-dd0e45c67d52
-- title:
--   §III C: optimal charge and leading-order comparisons
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   All logarithms are base two. Asymptotic inequalities are eventual bounds with positive constants chosen before the sizes, ancillary vectors, and erased sets over which they are uniform. For fixed $0<a<1$, $\alpha=an$ is imposed only along an admissible unbounded integer-size subsequence, with positive $k,t$; the threshold may depend on its little-o convergence rate.
--
--   The leading charge coefficient is minimized at $a=1/2$:
--   $$\frac12\le\frac1{4\sqrt{a(1-a)}}\quad(0<a<1).$$
--   For single erasure, even $n$, $\alpha=n/2$, and positive $k$ satisfying $k^2=o(n)$, eventually the expectation and exponential-tail bounds hold jointly with
--   $$B_{\rm Choi}=\frac{\sqrt k}{2n}(1+Ck^2/n),\qquad B_{\rm worst}=\frac{k}{2n}(1+Ck/n).$$
--
--   These are the paper's leading-order comparison upper bounds. The separately cited fundamental lower bounds are background.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 8, §III C: optimal charge and leading-order comparisons

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

/-- §III C, PDF p.8, (60)–(61): optimal leading charge a=1/2,
t=1, even n; the bound pair uses k²=o(n). Eq.(58)'s Choi reference is
a source cross-reference slip: Eq.(57) gives the same 1/(2n) at k=1. -/
theorem u1_optimal_charge (laws : PhysicalUnitaryLaws 2)
    (hlaw : ∀ n, IsCommutantHaarLaw (U1Group n) (laws n)) :
    (∀ a : ℝ, 0 < a → a < 1 → 1 / 2 ≤ 1 / (4 * Real.sqrt (a*(1-a)))) ∧
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N k : ℕ → ℕ,
    Tendsto N atTop atTop →
    Tendsto (fun i => (k i : ℝ)^2 / N i) atTop (nhds 0) →
    (∀ i, 0 < N i ∧ Even (N i) ∧ 0 < k i ∧ k i ≤ N i/2) →
    ∃ i0 : ℕ, ∀ i ≥ i0, ∀ h : k i ≤ N i,
    ∀ psi : EuclideanSpace ℂ (CovariantWord 2 (N i-k i)), ChargeState (N i/2) psi →
    ∀ S : Finset (Fin (N i)), S.card = 1 →
    let ec := fun U => choiError (noisyEncoder h (pureDensity psi) S U)
    let ew := fun U => optimalWorstRecoveryError (noisyEncoder h (pureDensity psi) S U)
    let bc := Real.sqrt (k i)/(2*N i)*(1+C*(k i : ℝ)^2/N i)
    let bw := (k i : ℝ)/(2*N i)*(1+C*(k i : ℝ)/N i)
    (∫ U, ec U ∂laws (N i)) ≤ bc ∧ (∫ U, ew U ∂laws (N i)) ≤ bw ∧
    (laws (N i)).real {U | bc < ec U ∨ bw < ew U} ≤ Real.exp (-c*N i) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
