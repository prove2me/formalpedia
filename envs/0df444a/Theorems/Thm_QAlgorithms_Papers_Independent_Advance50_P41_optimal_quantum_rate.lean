-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P41_optimal_quantum_rate
-- name    : QAlgorithms.Papers.Independent.Advance50.P41.optimal_quantum_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:05:17.372146+00:00
-- url     : https://prove2.me/theorems/de06239c-a748-4da0-8573-85fc2fc6a2a2
-- title:
--   Optimal quantum compression rate with unlimited entanglement
-- statement:
--   Let $\mathcal E=\{p(x),|\psi_x\rangle^A\otimes|\sigma_x\rangle^C\}$ be a countably supported ensemble with strictly positive probabilities summing to one and normalized pure vectors on finite-dimensional complex systems $A,C$. Let $Y=y(X)$ be the canonical orthogonal irreducible-component label of the joint $AC$ ensemble. Entropies $S$ use base-two logarithms and refer to the resulting source and its canonical $Y$ extension.
--
--   A block code uses arbitrary CPTP maps $A^nC^nA_0\to\widehat C^nM$ and $MB_0\to\widehat A^n$, fixed independently of the inaccessible input word, and an initial maximally entangled state of local dimension $K_n\ge1$. For every positive block length $n$, $1\le d_n=\dim M\le(\dim A)^n$. Write $Q_n=\log_2 d_n/n$, $E_n=\log_2 K_n/n$, and $F_n$ for the average joint root fidelity with the original $A^nC^n$ letters.
--
--   Put
--   $$q_*=\tfrac12\bigl(S(A)+S(ACY)-S(CY)\bigr),\qquad e_*=\tfrac12\bigl(S(A)-S(ACY)+S(CY)\bigr).$$
--   Every code sequence with $F_n\to1$ and $Q_n\to Q$ satisfies $Q\ge q_*$, with no assumption on convergence or boundedness of $E_n$. Moreover, one code sequence satisfies simultaneously
--   $$F_n\to1,\qquad Q_n\to q_*,\qquad E_n\to e_*.$$
--
--   Thus the unlimited-entanglement minimum is attained together with the specified entanglement-consumption rate.
-- source:
--   Entanglement-Assisted Quantum Data Compression, arXiv:1901.06346v1, PDF p. 2, Theorem 3; converse p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P41

open Filter

open scoped Topology BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A C : Type} [Fintype A] [Fintype C]

/-- Theorem 3, PDF p.2 (converse p.4): minimum unlimited-entanglement
quantum rate, with simultaneous achievability of the entanglement corner. -/
theorem optimal_quantum_rate [Countable X] (s : ProductPureSource X A C) (hs : s.Valid) :
    s.OptimalQuantumCorner s.quantumCorner s.entanglementCorner := by sorry

end QAlgorithms.Papers.Independent.Advance50.P41

end
