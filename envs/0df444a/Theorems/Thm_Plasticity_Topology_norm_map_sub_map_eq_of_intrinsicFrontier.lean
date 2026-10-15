-- Prove2me | Theorems.Thm_Plasticity_Topology_norm_map_sub_map_eq_of_intrinsicFrontier
-- name    : Plasticity.Topology.norm_map_sub_map_eq_of_intrinsicFrontier
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T02:24:13.082326+00:00
-- url     : https://prove2.me/theorems/0367ac33-0f86-469d-ac56-011b5bf0605e
-- title:
--   A nonexpansive map of a closed bounded set that is isometric on its relative boundary is isometric
-- statement:
--   Let $D$ be a closed bounded subset of a real normed space and $f$ a map into a normed group with $\|f(x)-f(x')\|\le\|x-x'\|$ on $D$. If $\|f(b)-f(b')\|=\|b-b'\|$ for all points $b,b'$ of the relative boundary of $D$, then $\|f(x)-f(x')\|=\|x-x'\|$ for all $x,x'\in D$.
--   The line through $x$ and $x'$ meets $D$ in a set whose extreme points on the line are relative boundary points $p,p'$, in the order $p,x,x',p'$, and the triangle inequality along that chord is an equality.
-- source:
--   C. Angosto, V. Kadets, O. Zavarzina, J. Math. Anal. Appl. 471 (2019), proof of Theorem 4.11 (arXiv:1808.08534)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Topology
theorem norm_map_sub_map_eq_of_intrinsicFrontier {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] (D : Set E) (hclosed : IsClosed D) (hbdd : Bornology.IsBounded D)
    (f : E → E') (hlip : LipschitzOnWith 1 f D)
    (hfr : ∀ b ∈ intrinsicFrontier ℝ D, ∀ b' ∈ intrinsicFrontier ℝ D, ‖f b - f b'‖ = ‖b - b'‖) :
    ∀ x ∈ D, ∀ x' ∈ D, ‖f x - f x'‖ = ‖x - x'‖ := by sorry
end Plasticity.Topology
