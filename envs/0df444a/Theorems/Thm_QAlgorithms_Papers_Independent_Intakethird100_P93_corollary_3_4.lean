-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_corollary_3_4
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.corollary_3_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:37:07.521815+00:00
-- url     : https://prove2.me/theorems/333ff317-72c5-4e7d-9f89-137e7fcb851a
-- title:
--   Injective boundary determines every bibundle by its type
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Assume $G_1=\{1\}$. The canonical projection identifies $G$ topologically and as a group with $t(G)=G/G_1$. For every $(H,G)$-bibundle $\pi:P\to M$ with structure map $\psi$ and type map $\varphi$, the canonical map gives
--
--   $$
--   G\cong t(G),\qquad
--   P\xrightarrow{\ \cong\ }\varphi^*H,\quad
--   p\longmapsto(\pi(p),\psi(p)).
--   $$
--
--   The second isomorphism preserves projection, right action and structure map. Both conclusions depend on the trivial-kernel assumption; no compactness or nonempty-base assumption is added.
--
--   Source correction: additionally require that the canonical map $\bar t:G/\ker(t)\to H$ is topologically inducing, so the quotient topology agrees with the subspace topology on $t(G)$. The printed local-section assumptions alone do not imply this; see correction.printed/changed/why and MODERATION-r1.md.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 11, Corollary 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Corollary 3.4, PDF p.11, both conclusions. With trivial kernel the
canonical G→G/ker(t)=t(G) is a topological group isomorphism, and the actual
map p↦(pi(p),psi(p)) identifies every bibundle with the type pullback. 
Source correction (topology): Printed: the claim uses the p.4 local-section
assumptions and identifies t(G)=G/ker(t) on p.7. Changed: htop explicitly
identifies the quotient topology with the image subspace topology. Why: those
local-section assumptions alone allow the identity R_discrete -> R_usual;
its inverse is not continuous. No closed-image condition is added.
-/
theorem corollary_3_4 (htop : Topology.IsInducing (QuotientGroup.kerLift C.t))
    {M P : Type u} [TopologicalSpace M] [TopologicalSpace P]
    (hker : C.t.ker = ⊥) (B : Bibundle C M P) :
    (∃ e : G ≃ₜ (G ⧸ C.t.ker),
      (∀ g, e g = QuotientGroup.mk g) ∧ ∀ g k, e (g * k) = e g * e k) ∧
    (∃ phi : C(M, TypeGroup C),
      (∀ p, phi (B.bundle.proj p) = typeProjection C (B.psi p)) ∧
      ∃ e : P ≃ₜ TypePullback C phi,
        (∀ p, (e p).val = (B.bundle.proj p, B.psi p)) ∧
        (∀ p g, (e (B.bundle.right.act p g)).val =
          (B.bundle.proj p, B.psi p * C.t g))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
