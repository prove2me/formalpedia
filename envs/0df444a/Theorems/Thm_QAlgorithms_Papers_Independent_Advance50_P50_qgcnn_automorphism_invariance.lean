-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_qgcnn_automorphism_invariance
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.qgcnn_automorphism_invariance
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:29:29.422777+00:00
-- url     : https://prove2.me/theorems/f4b863a1-36f2-4a09-b7d3-c2d94a5f6d2f
-- title:
--   Appendix G: tied QGCNN generators preserve graph automorphisms
-- statement:
--   Let $G$ be a fixed simple graph, $p$ an automorphism of its vertices, and $P$ its physical site-permutation matrix. Fix finite families of Hermitian one-qubit operators $O_r,R_s$ and real parameters $W_r,B_s$, tied across all vertices and edges. Count each unordered edge once and define
--
--   $$H=\sum_{\{i,j\}\in E(G)}\sum_rW_r O_r^{(i)}O_r^{(j)}+\sum_{v\in V(G)}\sum_sB_s R_s^{(v)}.$$
--
--   Then
--
--   $$PHP^\dagger=H.$$
--
--   This is the automorphism invariance of the Appendix G generator, adapted there from Ref.[32]. It supplies no full-permutation invariance for a generic fixed graph.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 29, Appendix G: tied QGCNN generators preserve graph automorphisms

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.29, Appendix G: tied generators commute with every graph
AUTOMORPHISM. This does not assert full-Sn equivariance for a fixed graph. -/
theorem qgcnn_automorphism_invariance {n a b : ℕ} (G : SimpleGraph (Fin n))
    (p : Equiv.Perm (Fin n)) (hp : ∀ i j, G.Adj (p i) (p j) ↔ G.Adj i j)
    (W : Fin a → ℝ) (B : Fin b → ℝ) (O : Fin a → Mat Bool) (R : Fin b → Mat Bool)
    (hO : ∀ r, (O r).IsHermitian) (hR : ∀ r, (R r).IsHermitian) :
    conjSuperop (sitePermutation p) (qgcnnGenerator G W B O R) = qgcnnGenerator G W B O R := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
