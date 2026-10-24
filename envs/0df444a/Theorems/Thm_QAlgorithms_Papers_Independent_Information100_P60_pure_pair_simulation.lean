-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_pure_pair_simulation
-- name    : QAlgorithms.Papers.Independent.Information100.P60.pure_pair_simulation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:47:22.949549+00:00
-- url     : https://prove2.me/theorems/7e20a042-f9c1-421d-9e03-122f66d592f4
-- title:
--   Appendix A, Proposition 4: pure-pair simulation for every O(3)-covariant channel
-- statement:
--   Let $\mathcal N$ be any $O(3)$-covariant CPTP map on qutrits, meaning $\mathcal N(OXO^T)=O\mathcal N(X)O^T$ for all real orthogonal $O$ and every operator $X$. For any normalized $|\psi_1\rangle,|\psi_2\rangle\in\mathbb C^3$, there exists a single mixed-unitary channel $\Phi$ such that $$\Phi(|\psi_i\rangle\langle\psi_i|)=\mathcal N(|\psi_i\rangle\langle\psi_i|)\qquad(i=1,2).$$ The vectors may coincide or differ only by phase. The channel may be mixed-unitary itself. This is simultaneous simulation for each pure-state pair.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 36, Appendix A, Proposition 4: pure-pair simulation for every O(3)-covariant channel

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF pp.36–39, Appendix A Proposition 4; coincident states and MU channels included. -/
theorem pure_pair_simulation (N : Maps 3 3) (hN : IsChannel N) (hc : OrthogonalCovariant N)
    (psi phi : EuclideanSpace ℂ (Fin 3)) (hp : ‖psi‖ = 1) (hq : ‖phi‖ = 1) :
    ∃ Phi ∈ MU 3, Phi (pureDensity psi) = N (pureDensity psi) ∧ Phi (pureDensity phi) = N (pureDensity phi) := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
