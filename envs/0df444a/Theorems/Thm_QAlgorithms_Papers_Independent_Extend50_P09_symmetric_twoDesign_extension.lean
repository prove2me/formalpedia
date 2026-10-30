-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_symmetric_twoDesign_extension
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.symmetric_twoDesign_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:30:38.167947+00:00
-- url     : https://prove2.me/theorems/50123e5a-4a96-4eca-8a8e-353da78b25bc
-- title:
--   §V: exact symmetric 2-design extension
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   Fix an integer $d\ge2$. For $n\ge2$ let $\lambda$ partition $n-1$ with at most $d$ rows, and let $l_\lambda,r_\lambda$ be the actual Schur and Specht module dimensions. Append the physical isotypic embedding of $I_{L_\lambda}/l_\lambda\otimes|\psi_\lambda\rangle\langle\psi_\lambda|$, where $\psi_\lambda$ is a fixed unit Specht vector, to one logical $d$-level system. Conjugate by Haar measure on the determinant-one commutant of the collective $SU(d)$ action and erase one fixed known site. Errors mean optimal CPTP recovery measured in root-fidelity purified distance, with normalized Choi input and a decoder chosen before the worst reference-entangled input.
--
--   Replace each Haar distribution by any probability law supported on its same commutant whose full physical first and second conjugation moments equal Haar moments. This includes joint cross-block moments and relative phases. Then all four main expectation and exponential-tail bounds continue to hold:
--   $$\text{Theorems 2, 3, 5 and 6 hold for exact symmetric unitary 2-designs.}$$
--
--   No approximate-design tolerance or circuit depth/size theorem is asserted; the SU(d) recovery proof caveat remains recorded.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 13, §V: exact symmetric 2-design extension

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

/-- §V, PDF p.13: full joint symmetric 2-design moments suffice for all
four main bounds. No convergence rate, depth or approximation tolerance. -/
theorem symmetric_twoDesign_extension
    (u1 h1 : PhysicalUnitaryLaws 2) (hU : ∀ n, DesignLaw (U1Group n) (u1 n) (h1 n))
    (d : ℕ) (hd : 2 ≤ d) (su hs : PhysicalUnitaryLaws d)
    (hS : ∀ n, DesignLaw (SUGroup d n) (su n) (hs n)) :
    U1Performance false u1 ∧ U1Performance true u1 ∧
    SUPerformance false d su ∧ SUPerformance true d su := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
