-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_proposition_3_3
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.proposition_3_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:36:48.998195+00:00
-- url     : https://prove2.me/theorems/382fbde3-3d09-4afb-865a-b87e80c53a99
-- title:
--   The kernel quotient is the type pullback of H
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Let $\pi:P\to M$ be an $(H,G)$-bibundle with structure map $\psi$. Its descended continuous type map $\varphi:M\to H/t(G)$ satisfies $\varphi(\pi(p))=[\psi(p)]$. There is a canonical $(H,t(G))$-bibundle isomorphism
--
--   $$
--   P/G_1\xrightarrow{\ \cong\ }\varphi^*H
--    =\{(m,h):\varphi(m)=[h]\},\qquad [p]\longmapsto(\pi(p),\psi(p)).
--   $$
--
--   The quotient and pullback have their quotient and subspace topologies, respectively. The map preserves the base, structure map and the induced right image-group action. This describes the actual kernel quotient rather than an unrelated bundle of the same type.
--
--   Source correction: additionally require that the canonical map $\bar t:G/\ker(t)\to H$ is topologically inducing, so the quotient topology agrees with the subspace topology on $t(G)$. The printed local-section assumptions alone do not imply this; see correction.printed/changed/why and MODERATION-r1.md.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 11, Proposition 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Proposition 3.3, PDF p.11. The quotient-to-pullback isomorphism is
[p]↦(pi(p),psi(p)). Its right structure group is t(G)=G/ker(t), correcting the
surrounding text's transposed (t(G),H). The actual descended type is constructed. 
Source correction (topology): Printed: the claim uses the p.4 local-section
assumptions and identifies t(G)=G/ker(t) on p.7. Changed: htop explicitly
identifies the quotient topology with the image subspace topology. Why: those
local-section assumptions alone allow the identity R_discrete -> R_usual;
its inverse is not continuous. No closed-image condition is added.
-/
theorem proposition_3_3 (htop : Topology.IsInducing (QuotientGroup.kerLift C.t))
    {M P : Type u} [TopologicalSpace M] [TopologicalSpace P]
    (B : Bibundle C M P) :
    ∃ phi : C(M, TypeGroup C),
      (∀ p, phi (B.bundle.proj p) = typeProjection C (B.psi p)) ∧
      ∃ e : OrbitSpace B.bundle.right C.t.ker ≃ₜ TypePullback C phi,
        (∀ p, (e (orbitClass B.bundle.right C.t.ker p)).val =
          (B.bundle.proj p, B.psi p)) ∧
        (∀ p g, (e (orbitClass B.bundle.right C.t.ker
          (B.bundle.right.act p g))).val =
          (B.bundle.proj p, B.psi p * C.t g)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
