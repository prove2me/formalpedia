-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_random_erasure_locations
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.random_erasure_locations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:32:54.677909+00:00
-- url     : https://prove2.me/theorems/da9de012-2905-44ab-b1bd-ef0465267953
-- title:
--   §VI: simultaneous locations and flagged random erasures
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   Fix an integer $d\ge2$. For $n\ge2$ let $\lambda$ partition $n-1$ with at most $d$ rows, and let $l_\lambda,r_\lambda$ be the actual Schur and Specht module dimensions. Append the physical isotypic embedding of $I_{L_\lambda}/l_\lambda\otimes|\psi_\lambda\rangle\langle\psi_\lambda|$, where $\psi_\lambda$ is a fixed unit Specht vector, to one logical $d$-level system. Conjugate by Haar measure on the determinant-one commutant of the collective $SU(d)$ action and erase one fixed known site. Errors mean optimal CPTP recovery measured in root-fidelity purified distance, with normalized Choi input and a decoder chosen before the worst reference-entangled input.
--
--   All logarithms are base two. Asymptotic inequalities are eventual bounds with positive constants chosen before the sizes, ancillary vectors, and erased sets over which they are uniform. For fixed $0<a<1$, $\alpha=an$ is imposed only along an admissible unbounded integer-size subsequence, with positive $k,t$; the threshold may depend on its little-o convergence rate.
--
--   In each U(1) main-theorem regime, and for SU(d) only at $t=1$, the corresponding bounds hold for arbitrary input-independent distributions $p_S\ge0$, $\sum_{|S|=t}p_S=1$, over erased sets whose location is flagged to the receiver. The same eventual numerical bound $B_n$ can be chosen so that
--   $$\mathbb E\epsilon(p)\le B_n,\qquad
--   \Pr[\exists S:\epsilon(S)>B_n\ \text{or}\ \exists p:\epsilon(p)>B_n]\le e^{-cn}.$$
--   Here either error criterion may be used with its own main-theorem bound. A good sampled encoder works for all locations simultaneously.
--
--   Permutation invariance is distributional and is not pointwise equality of fixed-encoder errors. No fixed independent-per-site erasure-rate theorem or multiple-erasure SU(d) performance is asserted.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 14, §VI: simultaneous locations and flagged random erasures

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

/-- §VI, PDF p.14: simultaneous locations and flagged mixtures. It is
the LAW that is permutation invariant, not each fixed appendUnitaryEncoder's error.
U(1)'s little-o regimes absorb the binomial union factor; SU(d) uses t=1. -/
theorem random_erasure_locations
    (u1 : PhysicalUnitaryLaws 2) (hU : ∀ n, IsCommutantHaarLaw (U1Group n) (u1 n))
    (d : ℕ) (hd : 2 ≤ d) (su : PhysicalUnitaryLaws d)
    (hS : ∀ n, IsCommutantHaarLaw (SUGroup d n) (su n)) :
    U1LocationPerformance false u1 ∧ U1LocationPerformance true u1 ∧
    SULocationPerformance false d su ∧ SULocationPerformance true d su := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
