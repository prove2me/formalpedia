-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P73_equivariant_strongFCofibration_iff_ndr
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P73.equivariant_strongFCofibration_iff_ndr
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:01:39.795995+00:00
-- url     : https://prove2.me/theorems/b85e517d-8fd5-4c12-a371-d151f3d72dfd
-- title:
--   Lemma 10: equivariant fiberwise NDR criterion
-- statement:
--   Let $B$ be a weakly Hausdorff k-space, let $G$ be a group object in $\mathcal K/B$, and let $i:A\hookrightarrow X$ be an equivariant inclusion of right $G$-spaces over $B$. A strong $\bar f$-cofibration means a map with the left lifting property against every equivariant map that is both a fiberwise homotopy equivalence and a fiberwise covering-homotopy fibration. Then
--
--   $$
--   i\text{ is a strong }\bar f\text{-cofibration}\quad\Longleftrightarrow\quad i(A)\text{ is closed in }X\text{ and }(X,i(A))\text{ is a }G\text{-fiberwise NDR pair}.
--   $$
--
--   Here an NDR representation consists of continuous maps $u:X\to I$ and $H:X\times I\to X$, with $I=[0,1]$, such that $i(A)=u^{-1}(0)$, $H(x,0)=x$, $H(a,t)=a$ for every $a\in i(A)$ and every $t\in I$, and $u(x)<1$ implies $H(x,1)\in i(A)$. The homotopy stays over $B$, $u(xg)=u(x)$, and $H(xg,t)=H(x,t)g$ for elements in a common fiber. Tensor and action domains have k-space topology. No fibrancy of $G$ is assumed.
--
--   This characterizes equivariant strong cofibrations by geometric deformation data.
--
--   **Formalization Note** An inclusion is represented by an embedding, with its image used as the subspace. The two sides of the equivalence have independent definitions.
-- source:
--   Simplicial principal bundles in parametrized spaces, arXiv:1203.2460v4, PDF p. 7, Lemma 10

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P73

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Intakethird100.P73

open CategoryTheory

open scoped Topology

/-- Roberts--Stevenson, Lemma 10, arXiv:1203.2460v4, PDF p. 7.
An equivariant inclusion over B is a strong fbar-cofibration exactly when
its image is closed and the pair has an equivariant fiberwise NDR
representation. No fibrancy assumption on the group is made. -/
theorem equivariant_strongFCofibration_iff_ndr
    (B : KSpace) (hB : IsWeaklyHausdorff B) (G : ParametrizedGroup B)
    (A X : EquivariantSpace G) (i : EquivariantMap A X)
    (hi : Topology.IsEmbedding i.map.map) :
    IsEquivariantStrongFCofibration i ↔
      IsClosed (Set.range i.map.map) ∧
      IsEquivariantFiberwiseNDR X (Set.range i.map.map) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P73

end
