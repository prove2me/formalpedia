-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_exact_3_3
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.exact_3_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:32:08.708206+00:00
-- url     : https://prove2.me/theorems/7d99fb1d-a904-4828-99d5-ae0bfb261e29
-- title:
--   Existence and reduction: exactness of (3.3)
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   For any base space $M$, let $\iota(Q)=Q\times_{G_1}G$, with $\psi([q,g])=t(g)$, for a principal $G_1$-bundle $Q$. Let $\operatorname{Type}(P):M\to H/t(G)$ be the type of an $(H,G)$-bibundle. Extension gives an injection on isomorphism classes, and its image consists precisely of the identically unit type classes:
--
--   $$
--   \iota(Q)\cong\iota(R)\iff Q\cong R,\qquad
--   \operatorname{Type}(P)\equiv1\iff \exists Q,\ P\cong\iota(Q).
--   $$
--
--   This is the set-level exactness of (3.3), including injectivity of the first map. Equality of classes is expressed here by geometric isomorphisms of their representatives; the extension quotient and all its maps are the actual ones. The assertion does not require every continuous type map to be realized.
--
--   Source correction: additionally require that the canonical map $\bar t:G/\ker(t)\to H$ is topologically inducing, so the quotient topology agrees with the subspace topology on $t(G)$. The printed local-section assumptions alone do not imply this; see correction.printed/changed/why and MODERATION-r1.md.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 12, §1 / §3, unnumbered main existence result: exactness of (3.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- The main existence statement (3.3), PDF p.12, previewed pp.1--2.
Equality of isomorphism classes is presented by geometric isomorphisms: the first
clause says precisely that the actual extension induces an injection on classes;
the second says its essential image is precisely the identically unit type. The
extension is Q×ker(t)G with structure map [q,g]↦t(g), not a free map variable.
No surjectivity of Type onto all continuous type maps is asserted. 
Source correction (topology): Printed: the claim uses the p.4 local-section
assumptions and identifies t(G)=G/ker(t) on p.7. Changed: htop explicitly
identifies the quotient topology with the image subspace topology. Why: those
local-section assumptions alone allow the identity R_discrete -> R_usual;
its inverse is not continuous. No closed-image condition is added.
-/
theorem exact_3_3 (htop : Topology.IsInducing (QuotientGroup.kerLift C.t))
    {M : Type u} [TopologicalSpace M] :
    (∀ (Q R : TopCat.{u}) (B : PrincipalBundle C.t.ker M Q)
      (D : PrincipalBundle C.t.ker M R),
      IotaIsomorphic C B D ↔ PrincipalIsomorphic B D) ∧
    (∀ (P : TopCat.{u}) (B : Bibundle C M P),
      HasUnitType C B ↔ ∃ (Q : TopCat.{u}) (R : PrincipalBundle C.t.ker M Q),
        IotaToBibundleIsomorphic C R B) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
