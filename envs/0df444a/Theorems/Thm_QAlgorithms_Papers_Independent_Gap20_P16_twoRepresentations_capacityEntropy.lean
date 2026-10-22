-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P16_twoRepresentations_capacityEntropy
-- name    : QAlgorithms.Papers.Independent.Gap20.P16.twoRepresentations_capacityEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:35:28.791047+00:00
-- url     : https://prove2.me/theorems/0a49ceb8-fee8-4737-8823-94f7d039b9a7
-- title:
--   Two irreducible covariance representations give the same capacity–entropy identity
-- statement:
--   Let $d\ge1$, let $\Phi$ be a completely positive trace-preserving map on the complex $d\times d$ matrices, and let $G$ be a compact Hausdorff topological group. Let $V^{(1)}$ and $V^{(2)}$ be irreducible projective unitary representations of $G$ on the same $\mathbb C^d$, each continuous through conjugation. If
--
--   $$
--   \Phi(V_g^{(1)}X V_g^{(1)*})=V_g^{(2)}\Phi(X)V_g^{(2)*}
--   \quad\text{for every }g\in G\text{ and every }X,
--   $$
--
--   then $\Phi(I)=I$ and
--
--   $$
--   \bar C^{(1)}(\Phi)=\log_2 d-\min_{\rho}H(\Phi(\rho)).
--   $$
--
--   The minimum ranges over density matrices and is attained. Entropy is in bits, and $\bar C^{(1)}$ is the attained maximum of the output Holevo quantity over all finite normalized state ensembles. This extends the capacity formula to distinct input and output covariance actions without changing their underlying space.
-- source:
--   Remarks on the classical capacity of quantum channel, arXiv:quant-ph/0212025v1, PDF p. 2, §1, (6)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P16

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

/-- PDF p.2, (6): both irreducible projective representations act on the
same d-dimensional space; the preceding whole conclusion remains valid. -/
theorem twoRepresentations_capacityEntropy
    {d : ℕ} (hd : 0 < d) {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (V1 V2 : ProjectiveRepresentation G d)
    (hirr1 : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun g => (V1.unitary g : Mat d)))
    (hirr2 : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun g => (V2.unitary g : Mat d)))
    (hcov : CovariantBetween Phi V1.unitary V2.unitary) :
    Phi 1 = 1 ∧ CapacityEntropyIdentity Phi := by sorry

end QAlgorithms.Papers.Independent.Gap20.P16

end
