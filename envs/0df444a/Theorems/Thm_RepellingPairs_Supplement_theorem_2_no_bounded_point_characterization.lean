-- Prove2me | Theorems.Thm_RepellingPairs_Supplement_theorem_2_no_bounded_point_characterization
-- name    : RepellingPairs.Supplement.theorem_2_no_bounded_point_characterization
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:58:47.460128+00:00
-- url     : https://prove2.me/theorems/1ff27146-0e42-4d92-af86-026c47c487cb
-- title:
--   Theorem 2 — outerplanar metrics have no bounded-point characterization
-- statement:
--   For every integer $k\ge 20$ there is a metric $D$ on $k$ terminals such that
--
--   1. $D$ is not outerplanar, and
--   2. for every proper subset $S\subsetneq T$ of the terminals, the restriction $D|_{S}$ is outerplanar.
--
--   Here a metric is outerplanar if some finite graph embedded in a closed disk, with every vertex on the boundary circle and with nonnegative edge lengths, realizes it on its terminals (Steiner vertices allowed, any order of the terminals around the circle).
--
--   Consequently no condition on boundedly many terminals at a time characterizes outerplanar metrics, in contrast with the four-point conditions for tree metrics and for Kalmanson metrics with a fixed cyclic order.
--
--   **Formalization Note** The terminals are $\{0,\dots,k-1\}$, and a metric has zero diagonal, is symmetric, is positive off the diagonal and satisfies the triangle inequality. Every subset $S\ne T$ is quantified, the empty set and the singletons included, and the restriction is $D$ on the subtype of $S$. The metric may depend on $k$; the specific witness used in Appendix A is not part of the statement.
--
--   Differences from the source:
--   - encoding: a metric on $k$ terminals → a metric on $\mathrm{Fin}\,k$ in the base mission's `IsMetric` (positive off the diagonal); reason: the terminals are an index set, and §1–2 of the paper use "metric" in this sense
--   - encoding: outerplanar (realized by a graph with all vertices on the boundary of the disk) → `OuterplanarRealizable` over an arbitrary finite terminal type with a disk embedding having every vertex on the unit circle and an injective terminal map; reason: the restriction to a subset needs a finite index type other than $\mathrm{Fin}\,k$; terminals are vertices, hence distinct; same instances
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), Theorem 2, p.3 (PDF p.4); proof in Appendix A, pp.36–38 (PDF pp.37–39)

import Mathlib
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_Supplement_OuterplanarRealizable

set_option autoImplicit false

namespace RepellingPairs

namespace Supplement

/-- **Theorem 2.** For every integer `k ≥ 20` there is a metric `D` on `k` terminals that is not
outerplanar, while the restriction of `D` to every proper subset of the terminals is outerplanar.
Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23,
2026), Theorem 2, p.3 (proof in Appendix A, pp.36–38).

**Formalization Note.** The terminals are `Fin k`; "metric" is `IsMetric` (zero diagonal, symmetric,
positive off the diagonal, triangle inequality). A proper subset is any `I ≠ univ`, the empty set and the
singletons included; the restriction is `D` on the subtype of `I`. Outerplanarity prescribes no order of
the terminals on the circle. The metric may depend on `k`. -/
theorem theorem_2_no_bounded_point_characterization :
    ∀ k : ℕ, 20 ≤ k → ∃ D : Fin k → Fin k → ℝ, IsMetric D ∧ ¬ OuterplanarRealizable D ∧
      ∀ I : Finset (Fin k), I ≠ Finset.univ →
        OuterplanarRealizable (fun a b : {x // x ∈ I} => D a.1 b.1) := by sorry

end Supplement

end RepellingPairs
