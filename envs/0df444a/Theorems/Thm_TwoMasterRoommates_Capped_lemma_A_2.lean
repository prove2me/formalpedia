-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_lemma_A_2
-- name    : TwoMasterRoommates.Capped.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:51:19.802543+00:00
-- url     : https://prove2.me/theorems/a1e1130b-2cf8-445b-b39e-fdd039c81689
-- title:
--   Lemma A.2 — disjoint bad intervals
-- statement:
--   Let $K$ be a finite mandatory marked-completion kernel and $M$ a stable cap-feasible completion. For every bad active $u$ associate the interval $[r(u),r(Mu))$. These intervals are pairwise disjoint. If $u$ is bad and $w\ne u$ is active with $r(u)<r(w)<r(Mu)$, then $w$ is marked, has a mandatory-token mate, and that mate has rank at most $r(u)$. Finally distinct positive edges have no actual endpoint in common:
--
--   $$[r(u),r(Mu))\cap[r(z),r(Mz))=\varnothing\qquad(u\ne z\text{ bad}).$$
--
--   Intervals may meet at the same rank boundary while using distinct actual identities. All three conclusions concern the original weak ranks and remain valid with arbitrary ties. This identifies the precise structure used in the residual criterion.
--
--   Differences from the source:
--   - generalization: real-valued weak ranks → ranks in any linear order; reason: finite attained values and their comparisons embed in the real source domain; specialize the rank type to the reals
--   - encoding: finite identity populations with arbitrary personal caps → finite labelled types, fixed-point-free involutions, and WithTop upper caps; reason: labels do not restrict populations; top is an infinite cap and every blocking comparison remains original and strict
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 9 (PDF p. 10), Lemma A.2

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Residual

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- Lemma A.2: all three disjointness and interior assertions, including rank ties. -/
theorem lemma_A_2 {ι R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder R]
    (K : Kernel ι R) (M : ι → ι) (hT : Mandatory K) (hM : KSolution K M) :
    (∀ u z, Bad K M u → Bad K M z → u ≠ z →
      Disjoint (Set.Ico (K.r u) (K.r (M u))) (Set.Ico (K.r z) (K.r (M z)))) ∧
    (∀ u w, Bad K M u → K.kind w = .active → w ≠ u →
      K.r u < K.r w → K.r w < K.r (M u) →
      K.marked w = true ∧ K.kind (M w) = .token ∧ K.r (M w) ≤ K.r u) ∧
    (∀ u z, Bad K M u → Bad K M z → u ≠ z →
      Disjoint ({u, M u} : Set ι) {z, M z}) := by sorry

end TwoMasterRoommates.Capped
