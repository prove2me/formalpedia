-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_proposition_3_8
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.proposition_3_8
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:38:32.575209+00:00
-- url     : https://prove2.me/theorems/8c732dac-a937-4d90-a325-88b91f6e6b8e
-- title:
--   A lifted type splits off a kernel bundle
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Let $P\to M$ be an $(H,G)$-bibundle with type $\varphi$, and suppose a continuous map $\widehat\varphi:M\to H$ satisfies $[\widehat\varphi(m)]=\varphi(m)$. There exists a principal $G_1$-bundle $R\to M$ such that
--
--   $$
--   P\cong\iota(R)(\widehat\varphi)=\iota(R)\otimes T(\widehat\varphi).
--   $$
--
--   In the underlying quotient $R\times_{G_1}G$, the twisted right action is $[r,g]\cdot k=[r,g\alpha(\widehat\varphi(m))(k)]$ and the structure map is $t(g)\widehat\varphi(m)$, where $m$ is the image of $r$. The isomorphism preserves this action, structure map and projection. Existence of $R$ is part of the conclusion, so the result gives a decomposition from a lift of the actual type.
--
--   Source correction: additionally require that the canonical map $\bar t:G/\ker(t)\to H$ is topologically inducing, so the quotient topology agrees with the subspace topology on $t(G)$. The printed local-section assumptions alone do not imply this; see correction.printed/changed/why and MODERATION-r1.md.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 13, Proposition 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Proposition 3.8, PDF p.13. R is an existential conclusion. The isomorphism
with ι(R)(lift) is pinned by its projection, twisted right action, and structure map.
The chosen lift projects to the actual type of P. 
Source correction (topology): Printed: the claim uses the p.4 local-section
assumptions and identifies t(G)=G/ker(t) on p.7. Changed: htop explicitly
identifies the quotient topology with the image subspace topology. Why: those
local-section assumptions alone allow the identity R_discrete -> R_usual;
its inverse is not continuous. No closed-image condition is added.
-/
theorem proposition_3_8 (htop : Topology.IsInducing (QuotientGroup.kerLift C.t))
    {M P : Type u} [TopologicalSpace M] [TopologicalSpace P]
    (B : Bibundle C M P) (lift : C(M, H))
    (hlift : ∀ p, typeProjection C (lift (B.bundle.proj p)) =
      typeProjection C (B.psi p)) :
    ∃ Q : TopCat.{u},
      ∃ R : PrincipalBundle C.t.ker M Q,
        ∃ e : IotaSpace C R ≃ₜ P,
          (∀ q g, B.bundle.proj (e (iotaClass C R q g)) = R.proj q) ∧
          (∀ q g k, e (iotaClass C R q
            (g * C.alpha (lift (R.proj q)) k)) =
            B.bundle.right.act (e (iotaClass C R q g)) k) ∧
          ∀ q g, B.psi (e (iotaClass C R q g)) =
            C.t g * lift (R.proj q) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
