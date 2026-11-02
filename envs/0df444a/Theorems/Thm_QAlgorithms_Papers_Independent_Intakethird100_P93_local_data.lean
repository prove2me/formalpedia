-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_local_data
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.local_data
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:39:06.976701+00:00
-- url     : https://prove2.me/theorems/e3442e00-2319-4487-88a8-1a2a96576135
-- title:
--   Continuous local cocycles extracted from a bibundle
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Let $\pi:P\to M$ be an $(H,G)$-bibundle with structure map $\psi$. There exist an open cover $\{U_i\}$, continuous local sections $s_i:U_i\to P$, continuous transition maps $g_{ij}:U_i\cap U_j\to G$, and continuous maps $h_i:U_i\to H$, such that $s_j=s_i g_{ij}$ and $h_i=\psi\circ s_i$. On every appropriate overlap,
--
--   $$
--   g_{ij}g_{jk}=g_{ik},\qquad h_j=h_i\,t(g_{ij}).
--   $$
--
--   The cover and all local data are conclusions, with maps defined on their actual subspaces. This describes the local geometric data without adding a cohomology-classification assertion for an unspecified equivalence relation.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 13, Note 3.2, local cocycle description

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Note 3.2, PDF pp.13--14: the actual bundle admits continuous local cocycle
data with sj=si gij and hi=psi∘si, satisfying both printed cocycle identities.
This makes no claim about an unspecified quotient cohomology classification. -/
theorem local_data {M P : Type u} [TopologicalSpace M] [TopologicalSpace P]
    (B : Bibundle C M P) : Nonempty (LocalCocycleData C B) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
