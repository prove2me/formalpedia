-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_lemma_2_10
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.lemma_2_10
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T06:35:14.81642+00:00
-- url     : https://prove2.me/theorems/a747022a-6dca-4f3e-acc5-036ff8decd89
-- title:
--   The unit-level set is precisely the unit-type reduction
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   For an $(H,G)$-bispace $(X,\psi)$ put $X_1=\{x\in X:\psi(x)=1\}$. Then
--
--   $$
--   X_1\ne\varnothing\iff\operatorname{Type}(X)=1.
--   $$
--
--   If $X_1$ is nonempty, it is a reduction to $(1,G_1)$: it is a single $G_1$-orbit and its structure map has value $1$. The assertion retains the possibility that $X_1$ is empty and supplies the reduction only when that condition is met.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 7, Lemma 2.10

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Lemma 2.10, PDF p.7, both clauses. No nonemptiness is imposed at nonunit type. -/
theorem lemma_2_10 {X : Type u} [TopologicalSpace X] (B : Bispace C X) :
    ((unitLevel C B).Nonempty ↔ bispaceType C B = unitType C) ∧
    ((unitLevel C B).Nonempty →
      IsReduction C B C.t.ker (⊥ : Subgroup H) (unitLevel C B)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
