-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_worst_concentration
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_worst_concentration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:23:13.668719+00:00
-- url     : https://prove2.me/theorems/1907576a-985d-4cd7-a426-87e21de21cf0
-- title:
--   Lemma 2: U(1) worst-error concentration
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   Let $\rho_{\rm avg}^{x,x}$ be the ensemble mean of the erased-register output for logical computational basis word $x$. Suppose a single density matrix $\zeta$, independent of $x$, obeys $P(\rho_{\rm avg}^{x,x},\zeta)\le\varepsilon$ for every $x$, where $\varepsilon\ge0$. Put $h=\min\{H_b(\alpha/n),H_b((\alpha+k)/n)\}$, with $H_b$ binary entropy. For every $\delta,\delta'>0$, there are universal $C>0$ and a nonnegative integer $b$, valid for all sufficiently large $n$, for which
--   $$\Pr[\epsilon_{\rm worst}>\varepsilon+\delta+2^k\sqrt{\delta'}]
--   \le\frac{Cn^b}{\delta}2^{k-nh/4+t/2}+\frac{Cn^b}{\delta'}2^{2k-nh/2+t}.$$
--
--   The polynomial factors represent the source's logarithmic remainders; these estimates may be uninformative at entropy endpoints.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 6, Lemma 2: U(1) worst-error concentration

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

/-- Lemma 2, PDF pp.6–7, (42)–(44). Polynomial prefactors express the
O(log n) log-probability remainder; Markov estimates are UPPER bounds. -/
theorem u1_worst_concentration :
    ∃ C : ℝ, 0 < C ∧ ∃ b n0 : ℕ, ∀ n ≥ n0, ∀ k alpha t : ℕ,
    ∀ hk : k ≤ n, alpha ≤ n-k → t ≤ n → 0 < n →
    ∀ psi : EuclideanSpace ℂ (CovariantWord 2 (n-k)), ChargeState alpha psi →
    ∀ S : Finset (Fin n), S.card = t →
    ∀ mu : Measure (Op (CovariantWord 2 n)), IsCommutantHaarLaw (U1Group n) mu →
    ∀ z : Op (RetainedConfigurations 2 n S), IsDensityMatrix z →
    ∀ epsilon delta deltaPrime : ℝ, 0 ≤ epsilon → 0 < delta → 0 < deltaPrime →
    (∀ x : CovariantWord 2 k,
      pdist (∫ U, retain S (appendUnitaryEncoder hk (pureDensity psi) U (pureDensity (ket x))) ∂mu) z ≤ epsilon) →
    let H := min (binEntropy2 ((alpha : ℝ)/n)) (binEntropy2 (((alpha+k : ℕ) : ℝ)/n))
    let p1 := C * (n : ℝ)^b * Real.rpow 2 ((k : ℝ)-(n : ℝ)/4*H+(t : ℝ)/2)/delta
    let p2 := C * (n : ℝ)^b * Real.rpow 2 (2*(k : ℝ)-(n : ℝ)/2*H+t)/deltaPrime
    mu.real {U | epsilon+delta+(2 : ℝ)^k*Real.sqrt deltaPrime <
      optimalWorstRecoveryError (noisyEncoder hk (pureDensity psi) S U)} ≤ p1+p2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
