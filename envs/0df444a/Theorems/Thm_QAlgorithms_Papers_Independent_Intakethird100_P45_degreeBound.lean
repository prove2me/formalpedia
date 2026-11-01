-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P45_degreeBound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P45.degreeBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:24:42.563992+00:00
-- url     : https://prove2.me/theorems/99936047-d098-4f31-ab0d-a2bc64b62906
-- title:
--   Endpoint-degree bound and the square-lattice maximum
-- statement:
--   In the one-slot heralded-loss model, retain at most one perfect EPR pair on each physical edge and use each memory in at most one pairwise BSM. Let $a\ne b$ be terminals of a finite square-grid network, let $d(a)$ and $d(b)$ be their physical degrees, and let $J$ be the actual integer number of delivered ebits for any chosen admissible schedule and any realization of its BSM flags. Then
--
--   $$J\le\min\{d(a),d(b)\}\le4.$$
--
--   For every two distinct sites of the full square lattice, four ebits are attainable in a single slot when the selected links and swaps all succeed: a sufficiently large finite portion contains a schedule of four edge-disjoint routes joining those sites. Terminals do not perform swaps for their own flow.
--
--   This identifies the maximum possible count on the unbounded grid, while retaining only an upper bound on arbitrary finite networks. It does not guarantee four successes at arbitrary loss parameters.
-- source:
--   Routing entanglement in the quantum internet, arXiv:1708.07142v2, PDF p. 4, §II.A: endpoint degree bounds the per-slot delivered count

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P45

namespace QAlgorithms.Papers.Independent.Intakethird100.P45

open scoped BigOperators

noncomputable section

/-- PDF pp.4–5: delivered count is at most either endpoint degree, hence four.
Four is attainable between any distinct lattice sites in a sufficiently large
finite portion of the lattice, when all selected operations succeed. This is
a possible count, not a four-ebit guarantee for arbitrary loss parameters.
Source correction (trap 30). Printed on p.4: the general-graph maximum is
min {d(a), d(b)}. Changed: an upper bound for finite grids, with four attained
for every distinct pair on the full lattice. Why: finite-grid bottlenecks can
prevent degree-bound attainment; p.5 uses only the upper bound, while Appendix A
pp.11–12 explicitly states full-lattice attainment. -/
theorem degreeBound :
    (∀ (N : ℕ) (G : GridNetwork N) (a b : Fin N), a ≠ b →
      ∀ (H : Finset (Edge N)), H ⊆ physicalEdges G →
      ∀ (F : Finset (PortTrailEncoding N)), FeasibleFamily H a b F →
      ∀ flags : InternalFlags N,
        deliveredCount F flags ≤ min (endpointDegree G a) (endpointDegree G b) ∧
        min (endpointDegree G a) (endpointDegree G b) ≤ 4) ∧
    (∀ A B : ℤ × ℤ, A ≠ B →
      ∃ (N : ℕ) (G : GridNetwork N) (a b : Fin N) (F : Finset (PortTrailEncoding N)),
        G.position a = A ∧ G.position b = B ∧
        FeasibleFamily (physicalEdges G) a b F ∧
        deliveredCount F (fun _ => true) = 4) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P45
