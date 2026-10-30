-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P41_visible_compression
-- name    : QAlgorithms.Papers.Independent.Advance50.P41.visible_compression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:12:58.168831+00:00
-- url     : https://prove2.me/theorems/7079e74e-b3e0-48c2-8ea2-606b249173fd
-- title:
--   Visible entanglement-assisted compression
-- statement:
--   Let $\mathcal E=\{p(x),|\psi_x\rangle^A\otimes|\sigma_x\rangle^C\}$ be a countably supported ensemble with strictly positive probabilities summing to one and normalized pure vectors on finite-dimensional complex systems $A,C$. Let $Y=y(X)$ be the canonical orthogonal irreducible-component label of the joint $AC$ ensemble. Entropies $S$ use base-two logarithms and refer to the resulting source and its canonical $Y$ extension.
--
--   A block code uses arbitrary CPTP maps $A^nC^nA_0\to\widehat C^nM$ and $MB_0\to\widehat A^n$, fixed independently of the inaccessible input word, and an initial maximally entangled state of local dimension $K_n\ge1$. For every positive block length $n$, $1\le d_n=\dim M\le(\dim A)^n$. Write $Q_n=\log_2 d_n/n$, $E_n=\log_2 K_n/n$, and $F_n$ for the average joint root fidelity with the original $A^nC^n$ letters.
--
--   Suppose the side vectors $|\sigma_x\rangle$ are orthonormal, so Alice can read the source label. The unlimited-entanglement quantum minimum and an attainable consumption corner are
--   $$q_*=e_*=\tfrac12S(A).$$
--   Every successful sequence with $Q_n\to Q$ obeys $Q\ge S(A)/2$, with no entanglement-rate convergence premise. One successful sequence attains both $Q_n\to S(A)/2$ and $E_n\to S(A)/2$. Every successful sequence with finite limits $Q,E$ satisfies
--   $$Q+E\ge S(A).$$
--
--   This specializes the operational quantum-message model to visible encoding.
-- source:
--   Entanglement-Assisted Quantum Data Compression, arXiv:1901.06346v1, PDF p. 5, Corollary 9

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P41

open Filter

open scoped Topology BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A C : Type} [Fintype A] [Fintype C]

/-- Corollary 9, PDF p.5: minimum visible quantum rate S(A)/2, simultaneous
E=S(A)/2 achievability, and the universal finite-rate sum converse. -/
theorem visible_compression [Countable X] (s : ProductPureSource X A C) (hs : s.Valid)
    (hvisible : s.Visible) :
    s.OptimalQuantumCorner (s.entropyA / 2) (s.entropyA / 2) ∧
    s.SumRateConverse := by sorry

end QAlgorithms.Papers.Independent.Advance50.P41

end
