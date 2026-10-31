-- Prove2me | Theorems.Thm_SweepingDesing_lemma_16
-- name    : SweepingDesing.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:23.188905+00:00
-- url     : https://prove2.me/theorems/f6f9aef8-ac13-4c7c-bd65-1e64820d1c30
-- title:
--   Lemma 16 — continuity of the talweg functions $\varphi^\uparrow$ and $\varphi$
-- statement:
--   Let $S:\mathbb R\rightrightarrows\mathbb R^n$ be a smooth sweeping process such that $S(t)$ is bounded for every $t\in\mathbb R$. Let $a,b\in\mathbb R$ with $[a,b]\subset\operatorname{dom}(S)$, and assume that the boundary-slice map $H_S$ is continuous on $[a,b]$ for the Pompeiu–Hausdorff metric. Then the oriented talweg $\varphi^\uparrow$ and the talweg $\varphi$ are continuous on $[a,b]$ as functions into $\mathbb R\cup\{+\infty\}$ with its usual topology.
--
--   The proof of Theorem A uses it to choose, at each time, a point of $S(t)$ where the oriented modulus is close to its maximum, uniformly in $t$.
--
--   Differences from the source:
--   - encoding: smooth sweeping process (Definition 10): a closed connected C¹ submanifold of ℝⁿ⁺¹ of dimension at most n, or a connected full-dimensional manifold with boundary whose boundary is a C¹ manifold of dimension n (closed graph, §3.1) → IsSmoothSweepingProcess: the graph is closed and connected and is cut out near each of its points by a C¹ submersion onto ℝ^{n+1−k} with one k ≤ n, or near each of its frontier points by {g ≤ 0} with g C¹ and dg ≠ 0; reason: the standard local description of C¹ embedded submanifolds and of full-dimensional closed regions with C¹ boundary; the same sets
--   - encoding: moduli and talwegs with values in ℝ ∪ {+∞}, sup ∅ = 0 → values in ℝ≥0∞ (ENNReal.ofReal a = a⁺), empty supremum 0; reason: the values are nonnegative; [0, +∞] carries the usual topology of ℝ ∪ {+∞} restricted to it
--   - encoding: H_S continuous for the Pompeiu–Hausdorff metric on [a, b] (in ℝⁿ⁺¹ with the Euclidean norm) → for every s ∈ [a, b], hausdorffEDist(H_S(s'), H_S(s)) → 0 as s' → s within [a, b], on ℝ × ℝⁿ with the max norm; reason: continuity of the restriction to [a, b]; an equivalent norm gives the same continuity
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Lemma 16, p.11

import Mathlib
import Definitions.Def_SweepingDesing_IsSmoothSweepingProcess
import Definitions.Def_SweepingDesing_boundarySlice
import Definitions.Def_SweepingDesing_orientedTalweg
import Definitions.Def_SweepingDesing_talweg
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Lemma 16, p.11 (continuity of the (oriented) talweg function): let `S` be a smooth
sweeping process with `S(t)` bounded for all `t ∈ ℝ`, and let `[a, b] ⊂ dom(S)` be such that `H_S`
is continuous for the Pompeiu–Hausdorff metric on `[a, b]`. Then the talweg functions `φ↑` and `φ`
are continuous on `[a, b]`, with values in `ℝ ∪ {+∞}` carrying its usual topology.

**Formalization Note** Continuity of `H_S` on `[a, b]` is continuity of its restriction to
`[a, b]` (limits within `[a, b]`), with `Metric.hausdorffEDist` on `ℝ × ℝⁿ`. -/
theorem lemma_16 {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (hS : IsSmoothSweepingProcess S)
    (hbdd : ∀ t, Bornology.IsBounded (S t)) (a b : ℝ) (hdom : ∀ t ∈ Icc a b, (S t).Nonempty)
    (hH : ∀ s ∈ Icc a b, Tendsto (fun s' => Metric.hausdorffEDist (boundarySlice S s')
      (boundarySlice S s)) (𝓝[Icc a b] s) (𝓝 0)) :
    ContinuousOn (orientedTalweg S) (Icc a b) ∧ ContinuousOn (talweg S) (Icc a b) := by sorry

end SweepingDesing
