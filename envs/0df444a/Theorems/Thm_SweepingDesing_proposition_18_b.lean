-- Prove2me | Theorems.Thm_SweepingDesing_proposition_18_b
-- name    : SweepingDesing.proposition_18_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:56.794086+00:00
-- url     : https://prove2.me/theorems/86a8cc82-60ab-49d7-8bc0-07ae62122fc6
-- title:
--   Proposition 18 b) — positive oriented modulus keeps orbits on $\partial\mathcal S$
-- statement:
--   Let $S:\mathbb R\rightrightarrows\mathbb R^n$ be a smooth sweeping process with graph $\mathcal S$, let $T=\sup\operatorname{dom}(S)$, fix $\bar t\in\operatorname{dom}(S)\setminus\{T\}$ and $\bar x\in S(\bar t)$. If $\|D^*S(\bar t,\bar x)|^+>0$, then for every $\tau>\bar t$ and every $\gamma\in\mathcal{AC}(S,[\bar t,\tau))$ with $\gamma(\bar t)=\bar x$ there exists $\delta>0$ such that
--
--   $$
--   \zeta(t):=(t,\gamma(t))\in\partial\mathcal S\qquad\text{for all }t\in[\bar t,\bar t+\delta).
--   $$
--
--   So an orbit started where the sets recede is pushed along the boundary of the graph for a while.
--
--   Differences from the source:
--   - encoding: smooth sweeping process (Definition 10): a closed connected C¹ submanifold of ℝⁿ⁺¹ of dimension at most n, or a connected full-dimensional manifold with boundary whose boundary is a C¹ manifold of dimension n (closed graph, §3.1) → IsSmoothSweepingProcess: the graph is closed and connected and is cut out near each of its points by a C¹ submersion onto ℝ^{n+1−k} with one k ≤ n, or near each of its frontier points by {g ≤ 0} with g C¹ and dg ≠ 0; reason: the standard local description of C¹ embedded submanifolds and of full-dimensional closed regions with C¹ boundary; the same sets
--   - encoding: t̄ ∈ dom(S) with t̄ < T = sup dom(S) (resp. t̄ ∈ dom(S) ∖ {T}) → S(t̄) ≠ ∅ and S(s) ≠ ∅ for some s > t̄; reason: T may be +∞; for t̄ ∈ dom(S) these are the same condition
--   - encoding: moduli and talwegs with values in ℝ ∪ {+∞}, sup ∅ = 0 → values in ℝ≥0∞ (ENNReal.ofReal a = a⁺), empty supremum 0; reason: the values are nonnegative; [0, +∞] carries the usual topology of ℝ ∪ {+∞} restricted to it
--   - reading: absolutely continuous on a (possibly non-compact) interval I → absolutely continuous on every compact interval [c, d] ⊆ I (IsLocallyAC); reason: the usual W^{1,1}_loc reading for [t, t+δ), [a, b), (a, b) and the pieces J_i; on a compact interval it is absolute continuity on I
--   - encoding: ℝⁿ⁺¹ with its Euclidean norm, time first → ℝ × EuclideanSpace ℝ (Fin n) with the max of the two norms; reason: normal cones, ∂𝒮 and Pompeiu–Hausdorff continuity do not change under an equivalent norm
--   - encoding: a curve γ : I → ℝⁿ with −γ̇(t) ∈ N_{S(t)}(γ(t)) for almost every t ∈ I → γ : ℝ → ℝⁿ, and for almost every t ∈ I there is v with HasDerivAt γ v t and −v ∈ N_{S(t)}(γ(t)); reason: values of γ off I play no role; almost every t ∈ I is an interior point of I at which an absolutely continuous curve is differentiable
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Proposition 18 b), p.12

import Mathlib
import Definitions.Def_SweepingDesing_IsSmoothSweepingProcess
import Definitions.Def_SweepingDesing_orientedModulus
import Definitions.Def_SweepingDesing_IsACOrbit
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Proposition 18 b), p.12 (geometric facts): let `S` be a smooth sweeping process, fix
`t̄ ∈ dom(S) ∖ {T}` and `x̄ ∈ S(t̄)`. If `‖D*S(t̄, x̄)|⁺ > 0`, then for any `τ > t̄` and
`γ ∈ 𝒜𝒞(S, [t̄, τ))` with `γ(t̄) = x̄` there exists `δ > 0` such that
`ζ(t) := (t, γ(t)) ∈ ∂𝒮` for all `t ∈ [t̄, t̄ + δ)`.

**Formalization Note** `∂𝒮 = frontier (gph S)`; absolute continuity on `[t̄, τ)` is read as on its
compact subintervals. -/
theorem proposition_18_b {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (hS : IsSmoothSweepingProcess S)
    (tbar : ℝ) (hT : ∃ s, tbar < s ∧ (S s).Nonempty) (xbar : EuclideanSpace ℝ (Fin n)) (hx : xbar ∈ S tbar)
    (hpos : 0 < orientedModulus S tbar xbar) :
    ∀ τ > tbar, ∀ γ : ℝ → EuclideanSpace ℝ (Fin n), IsACOrbit S γ (Ico tbar τ) → γ tbar = xbar →
      ∃ δ > (0 : ℝ), ∀ t ∈ Ico tbar (tbar + δ),
        (t, γ t) ∈ frontier (GenNewtonSubgrad.ProxReg.gph S) := by sorry

end SweepingDesing
