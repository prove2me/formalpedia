-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_proposition_2_6
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.proposition_2_6
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:33:30.376216+00:00
-- url     : https://prove2.me/theorems/f1dc92dd-5cb1-4aad-8eca-cb11164ff975
-- title:
--   Type classifies bispaces
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   For any two $(H,G)$-bispaces $(X,\psi)$ and $(Y,\chi)$, let $\operatorname{Type}(X)=[\psi(x)]$ and $\operatorname{Type}(Y)=[\chi(y)]$ in $H/t(G)$; equivariance makes the choices of points immaterial. Then
--
--   $$
--   X\cong Y\iff\operatorname{Type}(X)=\operatorname{Type}(Y).
--   $$
--
--   Here an isomorphism is a right equivariant homeomorphism $f:X\to Y$ satisfying $\chi\circ f=\psi$. The result distinguishes all bispace isomorphism classes by their type.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 5, Proposition 2.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Proposition 2.6, PDF p.5. Isomorphisms are homeomorphisms preserving both
the right action and psi. The proof's mis-typed chi=psi∘f is read as chi∘f=psi,
as in its own converse; no change to the printed proposition is needed. -/
theorem proposition_2_6 {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (B : Bispace C X) (D : Bispace C Y) :
    Nonempty (BispaceIso C B D) ↔ bispaceType C B = bispaceType C D := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
