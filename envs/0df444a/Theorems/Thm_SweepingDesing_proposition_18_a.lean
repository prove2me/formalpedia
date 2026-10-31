-- Prove2me | Theorems.Thm_SweepingDesing_proposition_18_a
-- name    : SweepingDesing.proposition_18_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:32.687907+00:00
-- url     : https://prove2.me/theorems/ffd293be-9d23-4036-8d46-a99d8c45a830
-- title:
--   Proposition 18 a) — a point that stays in $S(t)$ has nonpositive time-normals
-- statement:
--   Let $S:\mathbb R\rightrightarrows\mathbb R^n$ be a smooth sweeping process with graph $\mathcal S$, let $T=\sup\operatorname{dom}(S)$, fix $\bar t\in\operatorname{dom}(S)\setminus\{T\}$ and $\bar x\in S(\bar t)$. If there is $\delta>0$ such that $\bar x\in S(t)$ for all $t\in(\bar t,\bar t+\delta)$, then
--
--   $$
--   \alpha\le 0\qquad\text{for all }(\alpha,u)\in N_{\mathcal S}(\bar t,\bar x).
--   $$
--
--   Part a) of the geometric facts used to relate the oriented modulus with the motion of orbits.
--
--   Differences from the source:
--   - encoding: smooth sweeping process (Definition 10): a closed connected C¹ submanifold of ℝⁿ⁺¹ of dimension at most n, or a connected full-dimensional manifold with boundary whose boundary is a C¹ manifold of dimension n (closed graph, §3.1) → IsSmoothSweepingProcess: the graph is closed and connected and is cut out near each of its points by a C¹ submersion onto ℝ^{n+1−k} with one k ≤ n, or near each of its frontier points by {g ≤ 0} with g C¹ and dg ≠ 0; reason: the standard local description of C¹ embedded submanifolds and of full-dimensional closed regions with C¹ boundary; the same sets
--   - encoding: t̄ ∈ dom(S) with t̄ < T = sup dom(S) (resp. t̄ ∈ dom(S) ∖ {T}) → S(t̄) ≠ ∅ and S(s) ≠ ∅ for some s > t̄; reason: T may be +∞; for t̄ ∈ dom(S) these are the same condition
--   - encoding: ℝⁿ⁺¹ with its Euclidean norm, time first → ℝ × EuclideanSpace ℝ (Fin n) with the max of the two norms; reason: normal cones, ∂𝒮 and Pompeiu–Hausdorff continuity do not change under an equivalent norm
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Proposition 18 a), p.12

import Mathlib
import Definitions.Def_SweepingDesing_IsSmoothSweepingProcess
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Proposition 18 a), p.12 (geometric facts): let `S` be a smooth sweeping process, fix
`t̄ ∈ dom(S) ∖ {T}` and `x̄ ∈ S(t̄)`. If there is `δ > 0` such that `x̄ ∈ S(t)` for all
`t ∈ (t̄, t̄ + δ)`, then `α ≤ 0` for all `(α, u) ∈ N_𝒮(t̄, x̄)`.

**Formalization Note** `t̄ ∈ dom(S) ∖ {T}` with `T = sup dom(S)`: `x̄ ∈ S(t̄)` and some
`s > t̄` lies in `dom(S)`. `N_𝒮` is the limiting normal cone to `𝒮 = gph S` in `ℝ × ℝⁿ`. -/
theorem proposition_18_a {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (hS : IsSmoothSweepingProcess S)
    (tbar : ℝ) (hT : ∃ s, tbar < s ∧ (S s).Nonempty) (xbar : EuclideanSpace ℝ (Fin n)) (hx : xbar ∈ S tbar)
    (hstay : ∃ δ > (0 : ℝ), ∀ t ∈ Ioo tbar (tbar + δ), xbar ∈ S t) :
    ∀ p ∈ GenNewtonSubgrad.ProxReg.limNormal (GenNewtonSubgrad.ProxReg.gph S) (tbar, xbar),
      p.1 ≤ 0 := by sorry

end SweepingDesing
