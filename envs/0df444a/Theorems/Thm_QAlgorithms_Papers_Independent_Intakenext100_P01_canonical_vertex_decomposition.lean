-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_canonical_vertex_decomposition
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.canonical_vertex_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:11:53.940928+00:00
-- url     : https://prove2.me/theorems/e9f7b488-34aa-4d2b-a231-cad333f8ddd8
-- title:
--   Canonical decomposition from image vertices
-- statement:
--   Let $T:M_d(\mathbb C)\to M_n(\mathbb C)$ be a quantum channel, $d,n\ge1$, and let $\sigma_1,\ldots,\sigma_k$ be distinct vertices of its state image. No polytope assumption is imposed. Define $V_i$ as the complex span of all unit vectors $x$ with $T(xx^*)=\sigma_i$, and put $V=\sum_iV_i$ and $W=V^\perp$. The spaces $V_i$ are nonzero and mutually orthogonal, and
--   $$\mathbb C^d=\left(\bigoplus_i V_i\right)\oplus W,\qquad T(A)=T(P_VAP_V)+T(P_WAP_W)=\sum_i\operatorname{Tr}(P_{V_i}A)\sigma_i+T(P_WAP_W).$$
--   The restriction to $\operatorname{End}(V)$ is a basis-measurement map, hence a classical-quantum channel. The displayed identity holds on density matrices and on all operators by complex linearity. When $k=0$, $V=0$ and $W=\mathbb C^d$.
--
--   This identifies the actual restrictions of $T$ and the canonical subspaces used in Theorem 3.5.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 5, Proposition 3.4

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

/-- Proposition 3.4, PDF pp.5–6: canonical block decomposition, without a polytope
assumption. The restrictions are T on its compressed inputs, not unrelated chosen maps. -/
theorem canonical_vertex_decomposition {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (T : Superop (Fin d) (Fin n)) (hT : IsChannel T) :
    VertexDecompositionGeometry T := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
