-- Prove2me | Theorems.Thm_SweepingDesing_lemma_15
-- name    : SweepingDesing.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:23.210826+00:00
-- url     : https://prove2.me/theorems/b4b3ad56-b9dc-479d-a629-e04d7c0ba00c
-- title:
--   Lemma 15 — continuity of the oriented and symmetric moduli on $\partial\mathcal S$
-- statement:
--   Let $S:\mathbb R\rightrightarrows\mathbb R^n$ be a smooth sweeping process with graph $\mathcal S$. Then both functions
--
--   $$
--   (t,x)\mapsto\|D^*S(t,x)|^+\qquad\text{and}\qquad(t,x)\mapsto\|D^*S(t,x)\|^+
--   $$
--
--   are continuous on the boundary $\partial\mathcal S$, where the values are taken in $\mathbb R\cup\{+\infty\}$ with its usual topology.
--
--   This is the basic regularity fact behind the continuity of the talweg functions (Lemma 16) and the persistence of positive modulus along orbits (Proposition 18 b).
--
--   Differences from the source:
--   - encoding: smooth sweeping process (Definition 10): a closed connected C¹ submanifold of ℝⁿ⁺¹ of dimension at most n, or a connected full-dimensional manifold with boundary whose boundary is a C¹ manifold of dimension n (closed graph, §3.1) → IsSmoothSweepingProcess: the graph is closed and connected and is cut out near each of its points by a C¹ submersion onto ℝ^{n+1−k} with one k ≤ n, or near each of its frontier points by {g ≤ 0} with g C¹ and dg ≠ 0; reason: the standard local description of C¹ embedded submanifolds and of full-dimensional closed regions with C¹ boundary; the same sets
--   - encoding: moduli and talwegs with values in ℝ ∪ {+∞}, sup ∅ = 0 → values in ℝ≥0∞ (ENNReal.ofReal a = a⁺), empty supremum 0; reason: the values are nonnegative; [0, +∞] carries the usual topology of ℝ ∪ {+∞} restricted to it
--   - encoding: ℝⁿ⁺¹ with its Euclidean norm, time first → ℝ × EuclideanSpace ℝ (Fin n) with the max of the two norms; reason: normal cones, ∂𝒮 and Pompeiu–Hausdorff continuity do not change under an equivalent norm
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Lemma 15, p.11

import Mathlib
import Definitions.Def_SweepingDesing_IsSmoothSweepingProcess
import Definitions.Def_SweepingDesing_orientedModulus
import Definitions.Def_SweepingDesing_modulus
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Lemma 15, p.11 (continuity of the (oriented) modulus on `∂𝒮`): for a smooth sweeping
process `S`, the functions `(t, x) ↦ ‖D*S(t, x)|⁺` and `(t, x) ↦ ‖D*S(t, x)‖⁺` are continuous on
`∂𝒮` for the usual topology on `ℝ ∪ {+∞}`.

**Formalization Note** Both moduli take values in `[0, +∞]` with its order topology; `∂𝒮` is
`frontier (gph S)` in `ℝ × ℝⁿ`. -/
theorem lemma_15 {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (hS : IsSmoothSweepingProcess S) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => orientedModulus S p.1 p.2)
        (frontier (GenNewtonSubgrad.ProxReg.gph S)) ∧
      ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => modulus S p.1 p.2)
        (frontier (GenNewtonSubgrad.ProxReg.gph S)) := by sorry

end SweepingDesing
