-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_proposition_3_16
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.proposition_3_16
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:39:58.377195+00:00
-- url     : https://prove2.me/theorems/517f3c55-232a-4507-bcf9-c29565ec1991
-- title:
--   Contractible H supplies bibundle structures
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Assume that $H$ is contractible as an ordinary topological space. Let $M$ be paracompact Hausdorff and let $P\to M$ be any locally trivial principal $G$-bundle. Then there exists a continuous structure map
--
--   $$
--   \psi:P\to H,\qquad \psi(pg)=\psi(p)t(g),
--   $$
--
--   so that the given principal bundle admits an $(H,G)$-bibundle structure. The classifying context ensures numerability, and neither a prior structure map nor a classifying-map lift is assumed. Contractibility of $H$, not of $G$, is the required hypothesis.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 23, Proposition 3.16

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Proposition 3.16, PDF p.23. Contractibility is ordinary contractibility of H.
The conclusion supplies a continuous structure map on the given principal bundle;
no preassigned lift, section, or bibundle structure is assumed. -/
theorem proposition_3_16 {M P : Type u} [TopologicalSpace M] [ParacompactSpace M]
    [T2Space M] [TopologicalSpace P] [ContractibleSpace H]
    (R : PrincipalBundle G M P) :
    ∃ psi : C(P, H), ∀ p g, psi (R.right.act p g) = psi p * C.t g := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
