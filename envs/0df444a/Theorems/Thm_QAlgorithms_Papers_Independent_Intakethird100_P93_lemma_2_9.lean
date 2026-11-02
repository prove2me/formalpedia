-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_lemma_2_9
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.lemma_2_9
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:34:38.620731+00:00
-- url     : https://prove2.me/theorems/d0872de9-366e-47ea-ae49-254aece37c6f
-- title:
--   Quotient by the kernel is an image-group bispace
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Let $(X,\psi)$ be an $(H,G)$-bispace. Give $X/G_1$ its orbit quotient topology, and identify the image structure group $t(G)$ with $G/G_1$ with its quotient topology. The action and structure map descend to make $X/G_1$ an $(H,t(G))$-bispace:
--
--   $$
--   [x]\,[g]=[xg],\qquad \bar\psi([x])=\psi(x),\qquad
--   \bar\psi([x]\,[g])=\bar\psi([x])t(g).
--   $$
--
--   In particular, the descended continuous right action is principal for $G/G_1$. This records the correct structure group after killing the kernel; a free action of the original group is not asserted.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 7, Lemma 2.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Lemma 2.9, PDF p.7. The induced principal right action has structure group
G/ker(t), the image group with its quotient topology, rather than G itself.
Both descended maps are pinned on representatives. -/
theorem lemma_2_9 {X : Type u} [TopologicalSpace X] (B : Bispace C X) :
    ∃ R : RightAction (G ⧸ C.t.ker) (OrbitSpace B.right C.t.ker),
      IsRightTorsor R ∧
      ∃ psi : C(OrbitSpace B.right C.t.ker, H),
        (∀ x g, R.act (orbitClass B.right C.t.ker x)
          (QuotientGroup.mk g) = orbitClass B.right C.t.ker (B.right.act x g)) ∧
        (∀ x, psi (orbitClass B.right C.t.ker x) = B.psi x) ∧
        (∀ q k, psi (R.act q k) = psi q * QuotientGroup.kerLift C.t k) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
