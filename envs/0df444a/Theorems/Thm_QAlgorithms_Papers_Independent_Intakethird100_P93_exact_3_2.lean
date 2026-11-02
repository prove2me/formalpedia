-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_exact_3_2
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.exact_3_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:38:12.606736+00:00
-- url     : https://prove2.me/theorems/18c2c484-d3b4-476f-9d42-2e200ca894e5
-- title:
--   Categorical exactness: faithfulness and the unit-type image
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   For any base $M$, extend a principal $G_1$-bundle by $\iota(Q)=Q\times_{G_1}G$. A morphism $f:Q\to R$ is sent to $[q,g]\mapsto[f(q),g]$. This extension is faithful, and its essential image consists exactly of unit-type bibundles:
--
--   $$
--   \iota(f)=\iota(f')\Longrightarrow f=f',\qquad
--   \operatorname{Type}(P)\equiv1\iff\exists R,\ P\cong\iota(R).
--   $$
--
--   Morphisms are continuous right equivariant maps over $M$, and bibundle isomorphisms also preserve the structure map. These are precisely the two clauses called exactness in the source; fullness and a stronger higher kernel property are not asserted.
--
--   Source correction: additionally require that the canonical map $\bar t:G/\ker(t)\to H$ is topologically inducing, so the quotient topology agrees with the subspace topology on $t(G)$. The printed local-section assumptions alone do not imply this; see correction.printed/changed/why and MODERATION-r1.md.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 12, §3, categorical exactness (3.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Categorical exactness (3.2), PDF p.12, in exactly the two senses specified
by the source: faithfulness on Hom sets and the unit-type essential-image criterion.
Faithfulness is injectivity of the actual representativewise extension on maps;
full faithfulness is not asserted. 
Source correction (topology): Printed: the claim uses the p.4 local-section
assumptions and identifies t(G)=G/ker(t) on p.7. Changed: htop explicitly
identifies the quotient topology with the image subspace topology. Why: those
local-section assumptions alone allow the identity R_discrete -> R_usual;
its inverse is not continuous. No closed-image condition is added.
-/
theorem exact_3_2 (htop : Topology.IsInducing (QuotientGroup.kerLift C.t))
    {M : Type u} [TopologicalSpace M] :
    (∀ (Q R : TopCat.{u}) (B : PrincipalBundle C.t.ker M Q)
      (D : PrincipalBundle C.t.ker M R), Function.Injective (iotaHom C B D)) ∧
    (∀ (P : TopCat.{u}) (B : Bibundle C M P),
      HasUnitType C B ↔ ∃ (Q : TopCat.{u}) (R : PrincipalBundle C.t.ker M Q),
        IotaToBibundleIsomorphic C R B) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
