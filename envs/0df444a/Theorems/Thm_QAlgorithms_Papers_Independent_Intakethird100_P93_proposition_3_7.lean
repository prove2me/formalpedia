-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_proposition_3_7
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.proposition_3_7
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:37:51.10021+00:00
-- url     : https://prove2.me/theorems/d37a0560-292b-486b-918c-8f3a8964f904
-- title:
--   Extension detects trivial kernel bundles
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   For any principal $G_1$-bundle $Q\to M$, form the actual quotient extension $\iota(Q)=Q\times_{G_1}G$ with structure map $\psi([q,g])=t(g)$. Then
--
--   $$
--   Q\text{ is trivial as a }G_1\text{-bundle}
--   \iff\iota(Q)\text{ is trivial as an }(H,G)\text{-bibundle}.
--   $$
--
--   On the right the trivialization must preserve the structure map as well as the base and right action. The conclusion therefore detects the original kernel-bundle triviality, rather than the weaker triviality of an underlying $G$-bundle.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 11, Proposition 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Proposition 3.7, PDF p.11: ordinary G1-bundle triviality is equivalent to
bibundle triviality of the actual quotient extension, including its structure map. -/
theorem proposition_3_7 {M Q : Type u} [TopologicalSpace M] [TopologicalSpace Q]
    (R : PrincipalBundle C.t.ker M Q) :
    IsTrivialPrincipal R ↔ IsTrivialIota C R := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
