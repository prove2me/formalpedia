-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P16_irreduciblyCovariant_capacityEntropy
-- name    : QAlgorithms.Papers.Independent.Gap20.P16.irreduciblyCovariant_capacityEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:34:30.53345+00:00
-- url     : https://prove2.me/theorems/6adcac3e-7ae9-4ee5-b588-7c104342ab2a
-- title:
--   Irreducible covariance gives bistochasticity and the capacity–entropy identity
-- statement:
--   Let $d\ge1$ and let $\Phi$ be a completely positive trace-preserving map on the complex $d\times d$ matrices. Let $G$ be a compact Hausdorff topological group and let $g\mapsto V_g$ be an irreducible projective unitary representation on $\mathbb C^d$, continuous through conjugation. Suppose $\Phi(V_gXV_g^*)=V_g\Phi(X)V_g^*$ for every $g\in G$ and every matrix $X$. Then
--
--   $$
--   \Phi(I)=I,\qquad \bar C^{(1)}(\Phi)=\log_2d-\min_{\rho}H(\Phi(\rho)).
--   $$
--
--   Here $\rho$ ranges over all positive semidefinite matrices of trace one, $H$ is von Neumann entropy in bits, and $\bar C^{(1)}$ is the maximum of $H(\Phi(\sum_jp_j\rho_j))-\sum_jp_jH(\Phi(\rho_j))$ over all finite state ensembles with $p_j\ge0$ and $\sum_jp_j=1$. Both the minimum and a finite-ensemble maximum are attained. Irreducibility excludes every proper nonzero common invariant complex subspace. This identifies the one-use classical capacity through the least output entropy.
-- source:
--   Remarks on the classical capacity of quantum channel, arXiv:quant-ph/0212025v1, PDF p. 2, §1, theorem; (1)–(3)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P16

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

/-- PDF p.2 italicized theorem, with identity (2) on p.1. Compact groups
are Hausdorff, and projective continuity is continuity of conjugation. -/
theorem irreduciblyCovariant_capacityEntropy
    {d : ℕ} (hd : 0 < d) {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (V : ProjectiveRepresentation G d) (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun g => (V.unitary g : Mat d)))
    (hcov : CovariantBetween Phi V.unitary V.unitary) :
    Phi 1 = 1 ∧ CapacityEntropyIdentity Phi := by sorry

end QAlgorithms.Papers.Independent.Gap20.P16

end
