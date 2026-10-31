-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_state_polytope_realization
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.state_polytope_realization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:23:03.951192+00:00
-- url     : https://prove2.me/theorems/913ef294-3a7e-42cc-bb2f-5bd87ecad35c
-- title:
--   Every nonempty state polytope is a CQ image
-- statement:
--   Let $n,k\ge1$ and let $C\subseteq S_n$ be a polytope with exactly the distinct vertices $\sigma_1,\ldots,\sigma_k$, where $S_n$ is the density-matrix state space. There is an orthonormal basis $(e_i)$ of $\mathbb C^k$ such that the explicitly defined map
--   $$T(A)=\sum_{i=1}^{k}\langle e_i,Ae_i\rangle\sigma_i$$
--   is a classical-quantum quantum channel and $\operatorname{Im}T=C$.
--
--   The input dimension is chosen to be $k$; this makes no realization claim at a prescribed input dimension.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 6, §3, unnumbered: every state polytope is a CQ image

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- §3, unnumbered realization, PDF p.6: input dimension is the number of vertices;
there is no fixed-input-dimension claim. The basis-measurement map is constructed explicitly. -/
theorem state_polytope_realization {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (C : Set (Mat n)) (s : Fin k → Mat n) (hs : ∀ i, IsDensityMatrix (s i))
    (hVertices : HasVertices C s) :
    ∃ e : OrthonormalBasis (Fin k) ℂ (EuclideanSpace ℂ (Fin k)),
      IsChannel (cqMap e s) ∧ HasCQRepresentation (cqMap e s) ∧ channelImage (cqMap e s) = C := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
