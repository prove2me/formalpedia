-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_polytopic_image_characterization
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.polytopic_image_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:09:22.723321+00:00
-- url     : https://prove2.me/theorems/a4dd96b8-d8cb-4e15-a6c9-14c30619f5dc
-- title:
--   Channels with polytopic images
-- statement:
--   Let $d,n\ge1$ and let $T:M_d(\mathbb C)\to M_n(\mathbb C)$ be a quantum channel. Its image means its image on positive semidefinite trace-one matrices. If this image is a polytope with distinct vertices $\sigma_1,\ldots,\sigma_k$, define
--   $$V_i=\operatorname{span}_{\mathbb C}\{x:\|x\|=1,\ T(xx^*)=\sigma_i\},\qquad V=\bigoplus_i V_i,\quad W=V^\perp.$$
--   The spaces $V_i$ are nonzero and mutually orthogonal, and $V\oplus W=\mathbb C^d$. Writing $P_U$ for orthogonal projection and $\rho_U=P_U\rho P_U$, the actual restrictions $T_1=T|_{\operatorname{End}(V)}$ and $T_2=T|_{\operatorname{End}(W)}$ satisfy
--   $$T(\rho)=T_1(\rho_V)+T_2(\rho_W)=\sum_i\operatorname{Tr}(P_{V_i}\rho)\sigma_i+T_2(\rho_W),\qquad \operatorname{Im}T_2\subseteq\operatorname{Im}T_1,\quad \sigma_i\notin\operatorname{Im}T_2.$$
--   Here $T_1$ is classical-quantum. Conversely, any such orthogonal block representation with nonzero blocks and output matrices that are exactly the distinct extreme points of their convex hull has that hull as its image and those matrices as its vertices. A zero residual space is allowed and has empty state image.
--
--   This characterizes polytopic channel images, including the residual channel hidden behind the classical-quantum part.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 6, Theorem 3.5, Channels with polytopic images; seed and first informal theorem on p.2

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

/-- Theorem 3.5, PDF p.6 (informal seed: PDF pp.1–2): canonical forward
characterization and converse for every orthogonal block representation. -/
theorem polytopic_image_characterization {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (T : Superop (Fin d) (Fin n)) (hT : IsChannel T) : PolytopeGeometry T := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
