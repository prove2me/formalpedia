-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_lemma_2_11
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.lemma_2_11
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:35:51.444772+00:00
-- url     : https://prove2.me/theorems/7b98dfe8-5ef7-42c9-9021-f391aba1514d
-- title:
--   Extension reconstructs a reduced bispace
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Let $G_0\le G$ and $H_0\le H$ be a crossed submodule: $t(G_0)\subseteq H_0$ and $\alpha(H_0)$ preserves $G_0$ setwise. Let $X_0\subseteq X$ be a reduction of an $(H,G)$-bispace, meaning a single nonempty $G_0$-orbit with $\psi(X_0)\subseteq H_0$. Form $X_0(G)=X_0\times_{G_0}G$ using $(x,g)k=(xk,k^{-1}g)$. Then
--
--   $$
--   X_0(G)\longrightarrow X,\qquad [x,g]\longmapsto xg
--   $$
--
--   is a right equivariant homeomorphism preserving $\psi([x,g])=\psi(x)t(g)$. This identifies extension of the given reduction with the original bispace by the canonical map.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 7, Lemma 2.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Lemma 2.11, PDF p.7: the canonical map [x,g]↦xg is a homeomorphism,
right equivariant and structure preserving. The equations on representatives also
specify the descended action and structure map without assuming their existence. -/
theorem lemma_2_11 {X : Type u} [TopologicalSpace X] (B : Bispace C X)
    (K : Subgroup G) (L : Subgroup H) (S : Set X)
    (hsub : IsCrossedSubmodule C K L) (hred : IsReduction C B K L S) :
    ∃ e : ExtensionSpace B.right K S ≃ₜ X,
      (∀ x g, e (extensionClass B.right K S x g) = B.right.act x.val g) ∧
      (∀ x g k, e (extensionClass B.right K S x (g * k)) =
        B.right.act (e (extensionClass B.right K S x g)) k) ∧
      (∀ x g, B.psi (e (extensionClass B.right K S x g)) =
        B.psi x.val * C.t g) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
