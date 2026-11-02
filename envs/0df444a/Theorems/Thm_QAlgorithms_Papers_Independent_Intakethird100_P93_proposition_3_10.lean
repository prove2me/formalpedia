-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P93_proposition_3_10
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P93.proposition_3_10
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:39:38.060404+00:00
-- url     : https://prove2.me/theorems/eae49aaf-9e6c-4a7b-b05b-a61dab9cb219
-- title:
--   Type-preserving homotopies induce bibundle isomorphisms
-- statement:
--   Let $t:G\to H$ be a topological crossed module, with continuous action $\alpha:H\to\operatorname{Aut}(G)$. Thus $t(\alpha(h)g)=ht(g)h^{-1}$ and $\alpha(t(g))k=gkg^{-1}$. Put $G_1=\ker t$ and give both $G/G_1$ and $H/t(G)$ their quotient topologies. Assume their quotient projections admit continuous local sections. All actions, structure maps and isomorphisms below are continuous, all principal bundles are locally trivial, and a bispace has a nonempty principal homogeneous underlying right space.
--
--   Let $M$ be paracompact Hausdorff, let $P\to N$ be an $(H,G)$-bibundle with actual type map $\varphi:N\to H/t(G)$, and let $f_0,f_1:M\to N$ be continuous. Suppose a continuous homotopy $h:I\times M\to N$ joins them and satisfies $\varphi(h(s,m))=\varphi(f_0(m))$ for every $s\in I=[0,1]$ and $m\in M$. Then
--
--   $$
--   f_0^*P\cong f_1^*P
--   $$
--
--   as $(H,G)$-bibundles, preserving the base, right action and structure map. This is the homotopy-invariance statement in the slice over $H/t(G)$, with time-constant projected type imposed throughout the homotopy.
--
--   Source correction: additionally require that the canonical map $\bar t:G/\ker(t)\to H$ is topologically inducing, so the quotient topology agrees with the subspace topology on $t(G)$. The printed local-section assumptions alone do not imply this; see correction.printed/changed/why and MODERATION-r1.md.
-- source:
--   On the existence of bibundles, arXiv:1102.4388v2, PDF p. 16, Proposition 3.10

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P93

namespace QAlgorithms.Papers.Independent.Intakethird100.P93

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (C : CrossedModule G H)

/-- Proposition 3.10, PDF pp.15--17: only homotopies whose actual pulled-back
type is constant in time induce bibundle isomorphisms. Paracompactness and the
Hausdorff convention are retained. 
Source correction (topology): Printed: the claim uses the p.4 local-section
assumptions and identifies t(G)=G/ker(t) on p.7. Changed: htop explicitly
identifies the quotient topology with the image subspace topology. Why: those
local-section assumptions alone allow the identity R_discrete -> R_usual;
its inverse is not continuous. No closed-image condition is added.
-/
theorem proposition_3_10 (htop : Topology.IsInducing (QuotientGroup.kerLift C.t))
    {M N P : Type u} [TopologicalSpace M] [ParacompactSpace M]
    [T2Space M] [TopologicalSpace N] [TopologicalSpace P] (B : Bibundle C N P)
    (f0 f1 : C(M, N)) (h : f0.Homotopy f1)
    (htype : ∀ (s : unitInterval) (m : M) (p q : P),
      B.bundle.proj p = h (s, m) → B.bundle.proj q = f0 m →
      typeProjection C (B.psi p) = typeProjection C (B.psi q)) :
    PullbacksIsomorphic C B f0 f1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P93
