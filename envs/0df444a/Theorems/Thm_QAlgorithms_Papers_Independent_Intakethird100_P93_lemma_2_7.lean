-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_lemma_2_7
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.lemma_2_7
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:34:09.945427+00:00
-- url     : https://prove2.me/theorems/3d2071a6-1ee2-4593-bcdf-9e02c09cb794
-- title:
--   Canonical unit and contraction isomorphisms
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Let $(X,\psi)$ be an $(H,G)$-bispace, let $T=G$ with structure map $t$, and let $X^*$ have the same underlying space with structure map $\psi^{-1}$ and right action $x\cdot g=x\alpha(\psi(x))^{-1}(g^{-1})$. Tensor products are the balanced quotients $(x,y)k=(xk,k^{-1}y)$. There are canonical structure-preserving right equivariant homeomorphisms
--
--   $$
--   X\otimes T\cong X,\qquad T\otimes X\cong X,\qquad X\otimes X^*\cong T.
--   $$
--
--   The unit maps send $[x,g]$ to $xg$ and $[g,x]$ to $g\cdot x$. The contraction sends $[x,y]$ to the unique $g$ such that $g\cdot y=x$, with $t(g)=\psi(x)\psi(y)^{-1}$. These specified maps give the unit and dual identifications used in tensor constructions.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 6, Lemma 2.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Lemma 2.7, PDF p.6, all three canonical isomorphisms. Their formulas,
right equivariance and structure-map identities are asserted on representatives.
The contraction sends [x,y] to the unique g with gy=x. -/
theorem lemma_2_7 {X : Type u} [TopologicalSpace X] (B : Bispace C X) :
    (∃ e : RightUnitTensor C B ≃ₜ X,
      (∀ x g, e (Quot.mk _ (x, g)) = B.right.act x g) ∧
      (∀ x g k, e (Quot.mk _ (x, g * k)) =
        B.right.act (e (Quot.mk _ (x, g))) k) ∧
      (∀ x g, B.psi (e (Quot.mk _ (x, g))) = B.psi x * C.t g)) ∧
    (∃ e : LeftUnitTensor C B ≃ₜ X,
      (∀ g x, e (Quot.mk _ (g, x)) = inducedLeft C B g x) ∧
      (∀ g x k, e (Quot.mk _ (g, B.right.act x k)) =
        B.right.act (e (Quot.mk _ (g, x))) k) ∧
      (∀ g x, B.psi (e (Quot.mk _ (g, x))) = C.t g * B.psi x)) ∧
    (∃ e : DualTensor C B ≃ₜ G,
      (∀ x y, inducedLeft C B (e (Quot.mk _ (x, y))) y = x) ∧
      (∀ x y k, e (Quot.mk _ (x, inducedLeft C B k⁻¹ y)) =
        e (Quot.mk _ (x, y)) * k) ∧
      (∀ x y, C.t (e (Quot.mk _ (x, y))) = B.psi x * (B.psi y)⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
