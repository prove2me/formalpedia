-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P96_equivariantAutomorphisms_give_bibundle
-- name    : QAlgorithms.Papers.Independent.Intake100.P96.equivariantAutomorphisms_give_bibundle
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:57:16.646498+00:00
-- url     : https://prove2.me/theorems/b08c0332-048f-4e5c-bd43-8e14106faf93
-- title:
--   An equivariant smooth automorphism family supplies the right principal action
-- statement:
--   Let $p:E\to M$ be a smooth left principal bundle for a finite-dimensional real Lie group $H$, with Hausdorff paracompact base and total space. Suppose each $\phi_e$ is a smooth group automorphism of $H$ with smooth inverse, evaluation $(e,h)\mapsto\phi_e(h)$ is smooth, and
--
--   $$\phi_{k\cdot e}(h)=k\,\phi_e(h)\,k^{-1}\qquad(e\in E,\ k,h\in H).$$
--
--   There exists a smooth right principal $H$-action, preserving every fibre and commuting with the left action, whose value is
--
--   $$e\triangleleft h=\phi_e(h)\cdot e.$$
--
--   In particular this action, including its smooth local principal trivializations, turns the specified left bundle into an $H$-bibundle.
-- source:
--   Nonabelian Bundle Gerbes, their Differential Geometry and Gauge Theory, arXiv:hep-th/0312154v2, PDF p. 5, §2, unnumbered: equivariant automorphism description

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P96

open scoped Manifold ContDiff

namespace QAlgorithms.Papers.Independent.Intake100.P96

universe u v w z

section Bundles

variable {m h e : ℕ} {M : Type u} {H : Type v} {E : Type w}

variable [TopologicalSpace M] [ChartedSpace (RealModel m) M]

variable [TopologicalSpace H] [ChartedSpace (RealModel h) H]

variable [TopologicalSpace E] [ChartedSpace (RealModel e) E]

variable [Group H]

/-- Converse in the equivariant automorphism description, PDF p. 5, (4)–(6).
Automorphisms are algebraic MulAut values with smooth evaluation and smooth
individual inverses, so they are smooth group automorphisms, not bare MulAut.
Right principality, smoothness, and commuting actions are all conclusions. -/
theorem equivariantAutomorphisms_give_bibundle
    (B : LeftPrincipalBundle m h e M H E) (phi : E → MulAut H)
    (smoothEvaluation : ContMDiff ((realModel e).prod (realModel h)) (realModel h) ∞
      (fun q : E × H => phi q.1 q.2))
    (smoothInverse : ∀ q : E, ContMDiff (realModel h) (realModel h) ∞ (phi q).symm)
    (equivariant : ∀ q : E, ∀ k l : H,
      phi (B.leftAction k q) l = k * phi q l * k⁻¹) :
    ∃ R : RightPrincipalStructure B,
      ∀ q : E, ∀ k : H, R.rightAction q k = B.leftAction (phi q k) q := by sorry

end Bundles

end QAlgorithms.Papers.Independent.Intake100.P96
