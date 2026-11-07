-- Prove2me | Theorems.Thm_TreeCoverLB_theorem_4_3_padding
-- name    : TreeCoverLB.theorem_4_3_padding
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:10.194044+00:00
-- url     : https://prove2.me/theorems/521f85cc-fa11-402d-9679-413b20ad87cf
-- title:
--   Proof of Theorem 4.3: padding to $n$ points at distance $Q>\beta\,\mathrm{diam}$ keeps the stretch bound
-- statement:
--   Let $(X,d)$ be a finite nonempty metric space, $k\in\mathbb N$ and $\beta\ge 1$, and suppose every size-$k$ tree cover of $(X,d)$ has distortion at least $\beta$. Let $m\in\mathbb N$ and
--   $$
--   Q>\beta\cdot\operatorname{diam}(X)=\beta\max_{x,y\in X}d(x,y).
--   $$
--   Add $m$ new points so that every two distinct points, at least one of which is new, are at distance $Q$. Then
--
--   1. this defines a metric on $X\sqcup\{1,\dots,m\}$;
--   2. every size-$k$ tree cover of the enlarged metric has distortion at least $\beta$.
--
--   This is how the paper passes from the family $X_r$ to exactly $n$ points.
--
--   Differences from the source:
--   - generalization: the metric (X_r, d_r) with its stretch bound β_r = (c₀/M) r → any finite nonempty metric all of whose size-k tree covers have distortion ≥ β, with β ≥ 1; reason: the paper's instance satisfies β_r ≥ 1 for the large r it uses; 'This defines a metric' needs 2Q ≥ diam(X) (two points at distance 1, β = 1/4, Q = 1/3 violate the triangle inequality through a new point)
--   - encoding: Q > β · diam(X_r) = β · max_{x,y} d_r(x, y) → β · d(x, y) < Q for all x, y; reason: equivalent for β ≥ 0 on a finite nonempty X
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), proof of Theorem 4.3, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_TreeCoverLB_IsFinMetric
import Definitions.Def_TreeCoverLB_WeightedTree
import Definitions.Def_TreeCoverLB_IsTreeCover
import Definitions.Def_TreeCoverLB_padMetric

open Classical

namespace TreeCoverLB

/-- **Proof of Theorem 4.3 — padding to `n` points** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), proof of Theorem 4.3, p.17 (PDF p.19)):
let `(X, d)` be a finite nonempty metric space every size-`k` tree cover of which has distortion at
least `β ≥ 1`. Add `m` new points so that the distance between every two distinct points, at least
one of which is new, is a common value `Q > β · diam(X)`. Then this defines a metric, and every
size-`k` tree cover of the enlarged metric has distortion at least `β`.

**Formalization Note** `Q > β · diam(X) = β · max_{x,y} d(x, y)` is written `∀ x y, β d(x, y) < Q`
(equivalent for `β ≥ 0` on a finite nonempty `X`). The hypothesis `β ≥ 1` is added: the paper's
`β_r = (c₀/M) r` tends to infinity and is at least `1` for the large `r` it uses, and the clause
"This defines a metric" needs `2Q ≥ diam(X)` (two points at distance `1`, `β = 1/4`, `Q = 1/3` break
the triangle inequality through a new point). -/
theorem theorem_4_3_padding {X : Type*} [Fintype X] [Nonempty X] (d : X → X → ℝ)
    (hd : IsFinMetric d) (k : ℕ) (β : ℝ) (hβ : 1 ≤ β)
    (hcov : ∀ (T : Fin k → WeightedTree X) (α : ℝ), IsTreeCover d T α → β ≤ α)
    (m : ℕ) (Q : ℝ) (hQ : ∀ x y, β * d x y < Q) :
    IsFinMetric (padMetric (m := m) d Q) ∧
      ∀ (T : Fin k → WeightedTree (X ⊕ Fin m)) (α : ℝ),
        IsTreeCover (padMetric (m := m) d Q) T α → β ≤ α := by sorry

end TreeCoverLB
