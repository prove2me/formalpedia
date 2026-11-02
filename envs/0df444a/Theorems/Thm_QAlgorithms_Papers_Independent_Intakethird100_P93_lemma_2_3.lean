-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_lemma_2_3
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.lemma_2_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:32:50.745196+00:00
-- url     : https://prove2.me/theorems/579456d1-f44f-4014-9ce9-4e9a6d057fa2
-- title:
--   A crossed-module bispace induces a G-bispace
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Let $(X,\psi)$ be an $(H,G)$-bispace with right action denoted by $xg$. Define
--
--   $$
--   g\cdot x=x\,\alpha(\psi(x))^{-1}(g).
--   $$
--
--   This is a continuous left action, its orbit maps are homeomorphisms $G\to X$, and it commutes with the given right action. Together the two principal actions make $X$ a $G$-bispace with structure map $\alpha\circ\psi$, so $xg=\alpha(\psi(x))(g)\cdot x$. This constructs the induced bispace rather than assuming its axioms.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 4, Lemma 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Lemma 2.3, PDF p.4: formula (2.1) defines commuting principal left and right
actions, with G-bispace structure map alpha∘psi. -/
theorem lemma_2_3 {X : Type u} [TopologicalSpace X] (B : Bispace C X) :
    IsInducedGBispace C B := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
