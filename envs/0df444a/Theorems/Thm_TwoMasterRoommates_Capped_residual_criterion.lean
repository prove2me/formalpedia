-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_residual_criterion
-- name    : TwoMasterRoommates.Capped.residual_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:51:57.802489+00:00
-- url     : https://prove2.me/theorems/604aa32b-884a-4789-b6e1-54a2af41da53
-- title:
--   §A.1 — exact residual completion criterion
-- statement:
--   Let $K$ be a finite mandatory kernel. Fix admissible positive edges $F$ and equal-rank active edges $L$: their endpoints and positive intervals are disjoint, they pass their type and cap tests, equal-rank edges avoid strict positive interiors, and every remaining active is marked. There is a stable completion having exactly these positive and equal-rank active edges if and only if the remaining tokens admit a deadline-respecting bijection to the remaining actives:
--
--   $$\exists M\text{ completing }(F,L)\quad\Longleftrightarrow\quad\exists\sigma:T_{\mathrm{res}}\simeq W_{\mathrm{res}},\quad r(s)\le d_F(\sigma(s))\quad\forall s.$$
--
--   In addition, every stable completion yields admissible families by extracting its own positive and equal-rank edges, and its residual token assignment satisfies these deadlines. Here $d_F$ is the printed piecewise deadline, not a condition restating stability. This gives both sufficiency and necessity of the local reduction.
--
--   Differences from the source:
--   - generalization: real-valued weak ranks → ranks in any linear order; reason: finite attained values and their comparisons embed in the real source domain; specialize the rank type to the reals
--   - encoding: finite identity populations with arbitrary personal caps → finite labelled types, fixed-point-free involutions, and WithTop upper caps; reason: labels do not restrict populations; top is an infinite cap and every blocking comparison remains original and strict
--   - encoding: unordered equal-rank edges → one oriented representative chosen by a fixed identity order; reason: every finite labelled population has such an order and each edge is represented once
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), pp. 9–10 (PDF pp. 10–11), §A.1 residual criterion and its sufficiency/necessity paragraph

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Residual

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- §A.1, pp. 9–10: exact residual criterion, including extraction from every completion. -/
theorem residual_criterion {ι R : Type} [Fintype ι] [LinearOrder ι] [LinearOrder R]
    (K : Kernel ι R) (hT : Mandatory K) :
    (∀ (F L : Finset (ι × ι)), AdmissibleFamilies K F L →
      ((∃ M, KSolution K M ∧ positiveEdges K M = F ∧ equalEdges K M = L) ↔
        ResidualAssignment K F L)) ∧
    (∀ M, KSolution K M →
      AdmissibleFamilies K (positiveEdges K M) (equalEdges K M) ∧
      ResidualAssignment K (positiveEdges K M) (equalEdges K M)) := by sorry

end TwoMasterRoommates.Capped
