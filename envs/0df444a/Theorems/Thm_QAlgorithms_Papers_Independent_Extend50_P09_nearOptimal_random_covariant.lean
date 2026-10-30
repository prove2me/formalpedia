-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_nearOptimal_random_covariant
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.nearOptimal_random_covariant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:20:29.586983+00:00
-- url     : https://prove2.me/theorems/484f0d63-aa36-4ace-a07c-9ad8a369bd44
-- title:
--   Abstract / paper result: near-optimal random covariant codes
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   Fix an integer $d\ge2$. For $n\ge2$ let $\lambda$ partition $n-1$ with at most $d$ rows, and let $l_\lambda,r_\lambda$ be the actual Schur and Specht module dimensions. Append the physical isotypic embedding of $I_{L_\lambda}/l_\lambda\otimes|\psi_\lambda\rangle\langle\psi_\lambda|$, where $\psi_\lambda$ is a fixed unit Specht vector, to one logical $d$-level system. Conjugate by Haar measure on the determinant-one commutant of the collective $SU(d)$ action and erase one fixed known site. Errors mean optimal CPTP recovery measured in root-fidelity purified distance, with normalized Choi input and a decoder chosen before the worst reference-entangled input.
--
--   All logarithms are base two. Asymptotic inequalities are eventual bounds with positive constants chosen before the sizes, ancillary vectors, and erased sets over which they are uniform. For fixed $0<a<1$, $\alpha=an$ is imposed only along an admissible unbounded integer-size subsequence, with positive $k,t$; the threshold may depend on its little-o convergence rate.
--
--   For the U(1) construction the two error bounds are
--   $$\mathbb E\epsilon_{\rm Choi}\le\frac{\sqrt{tk}}{4n\sqrt{a(1-a)}}\left(1+O(k^2t^2/n)\right),\qquad
--   \mathbb E\epsilon_{\rm worst}\le\frac{k\sqrt t}{4n\sqrt{a(1-a)}}\left(1+O(kt^2/n)\right),$$
--   under $k^2t^2=o(n)$ and $kt^2=o(n)$, respectively. For the SU(d) construction, if $n-\lambda_1\ge\eta n$ for fixed $\eta>0$, both errors have expectation at most $\sqrt{d^2-1}/(2n)+O(n^{-2})$. Each corresponding bound holds except on a set of probability at most $e^{-cn}$ for some $c>0$.
--
--   This packages the four main results and makes no circuit-efficiency claim. The SU(d) recovery claims retain the proof caveat recorded in the notes.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 1, Abstract / paper result: near-optimal random covariant codes

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

/-- Abstract, PDF p.1, pinned by Theorems 2,3,5,6, pp.5,7,11–12.
The umbrella result consists of those two constructions and their exact regimes;
no efficient circuit construction or new lower bound is asserted. -/
theorem nearOptimal_random_covariant
    (u1 : PhysicalUnitaryLaws 2) (hu1 : ∀ n, IsCommutantHaarLaw (U1Group n) (u1 n))
    (d : ℕ) (hd : 2 ≤ d) (su : PhysicalUnitaryLaws d)
    (hsu : ∀ n, IsCommutantHaarLaw (SUGroup d n) (su n)) :
    U1Performance false u1 ∧ U1Performance true u1 ∧
    SUPerformance false d su ∧ SUPerformance true d su := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
