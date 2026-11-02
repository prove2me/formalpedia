-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_lemma_2_12
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.lemma_2_12
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:36:19.790915+00:00
-- url     : https://prove2.me/theorems/44696765-68cc-43f3-8c79-91f8a77117fd
-- title:
--   A unit-type bispace is reconstructed from its unit level
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Let $(X,\psi)$ be an $(H,G)$-bispace with $\operatorname{Type}(X)=1$, and put $X_1=\psi^{-1}(1)$. Then the actual extension from $G_1$ reconstructs $X$:
--
--   $$
--   X_1\times_{G_1}G\xrightarrow{\ \cong\ } X,\qquad [x,g]\longmapsto xg.
--   $$
--
--   This is a right equivariant homeomorphism with structure map $\psi([x,g])=t(g)$. Neither the existence of the reduction nor a reconstruction isomorphism is an input; both are consequences of the unit-type condition.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 8, Lemma 2.12

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Lemma 2.12, PDF p.8: reconstruct from the actual unit-level set, by [x,g]↦xg.
No reduction or reconstruction is assumed as a hypothesis. -/
theorem lemma_2_12 {X : Type u} [TopologicalSpace X] (B : Bispace C X)
    (htype : bispaceType C B = unitType C) :
    ∃ e : ExtensionSpace B.right C.t.ker (unitLevel C B) ≃ₜ X,
      (∀ x g, e (extensionClass B.right C.t.ker (unitLevel C B) x g) =
        B.right.act x.val g) ∧
      (∀ x g k, e (extensionClass B.right C.t.ker (unitLevel C B) x (g * k)) =
        B.right.act (e (extensionClass B.right C.t.ker (unitLevel C B) x g)) k) ∧
      (∀ x g, B.psi (e (extensionClass B.right C.t.ker (unitLevel C B) x g)) =
        C.t g) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
