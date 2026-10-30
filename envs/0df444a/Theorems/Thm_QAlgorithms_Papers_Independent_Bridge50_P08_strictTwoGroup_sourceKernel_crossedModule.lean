-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P08_strictTwoGroup_sourceKernel_crossedModule
-- name    : QAlgorithms.Papers.Independent.Bridge50.P08.strictTwoGroup_sourceKernel_crossedModule
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:16:42.363957+00:00
-- url     : https://prove2.me/theorems/d6a73b66-4bff-4a1f-9a16-2e1336b5d014
-- title:
--   Source kernels of strict 2-groups are crossed modules
-- statement:
--   Let $G$ be the object group and $K$ the tensor group of arrows of a strict 2-group, with source and target homomorphisms $s,t:K\to G$ and identity homomorphism $i:G\to K$. Let $H=\ker(s)$. Restrict $t$ to obtain $\beta:H\to G$, and set $\alpha(g)h=i(g)h i(g)^{-1}$. Then this specified action and homomorphism form a crossed module: for every $g\in G$ and $h,k\in H$,
--
--   $$\beta(\alpha(g)h)=g\beta(h)g^{-1},\qquad \alpha(\beta(h))k=hkh^{-1}.$$
--
--   This recovers the algebraic crossed module from the given strict 2-group. It does not assert that the source kernel is a Lie subgroup.
-- source:
--   Principal 2-bundles and their gauge 2-groups, arXiv:0803.3692v4, PDF p. 10, Remark II.4: source kernel yields a crossed module

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P08

namespace QAlgorithms.Papers.Independent.Bridge50.P08

open Set Filter Topology

open QAlgorithms.Papers.Independent.Renew46.P18

open QAlgorithms.Papers.Independent.Claimed50.P22

open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

/-- Remark II.4, PDF p. 10: the converse algebraic construction has
H = ker(s), beta = t restricted to ker(s), and the identity-conjugation
action. Both crossed-module axioms are conclusions. No Lie subgroup or
smoothness of the kernel is asserted. -/
theorem strictTwoGroup_sourceKernel_crossedModule
    {G : Type u} {K : Type v} [Group G] [Group K]
    (s t : K →* G) (identity : G →* K)
    (comp : K → K → K) (arrowInv : K → K)
    (h : IsStrictTwoGroup s t identity comp arrowInv) :
    IsCrossedModule (t.comp s.ker.subtype)
      (sourceKernelAction s identity (fun g => (h.1 g).1)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P08
