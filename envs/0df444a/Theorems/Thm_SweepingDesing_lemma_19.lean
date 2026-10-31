-- Prove2me | Theorems.Thm_SweepingDesing_lemma_19
-- name    : SweepingDesing.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:07.763064+00:00
-- url     : https://prove2.me/theorems/86135c56-6851-4223-9043-b7b743bf4d50
-- title:
--   Lemma 19 — the speed of an orbit equals the oriented modulus
-- statement:
--   Let $S:\mathbb R\rightrightarrows\mathbb R^n$ be a smooth sweeping process, $a,b\in\mathbb R$, and $\gamma\in\mathcal{AC}(S,[a,b))$. Then
--
--   $$
--   \|\dot\gamma(t)\|=\|D^*S(t,\gamma(t))|^+
--   $$
--
--   for every $t\in[a,b)$ at which $\gamma$ is differentiable, $-\dot\gamma(t)\in N_{S(t)}(\gamma(t))$, and $\|D^*S(t,\gamma(t))|^+$ is finite.
--
--   This identity converts length bounds for orbits into integral bounds for the oriented talweg and back; it is the link between the dynamic clauses b), c) and the static clauses a), d) of Theorem A.
--
--   Differences from the source:
--   - encoding: smooth sweeping process (Definition 10): a closed connected C¹ submanifold of ℝⁿ⁺¹ of dimension at most n, or a connected full-dimensional manifold with boundary whose boundary is a C¹ manifold of dimension n (closed graph, §3.1) → IsSmoothSweepingProcess: the graph is closed and connected and is cut out near each of its points by a C¹ submersion onto ℝ^{n+1−k} with one k ≤ n, or near each of its frontier points by {g ≤ 0} with g C¹ and dg ≠ 0; reason: the standard local description of C¹ embedded submanifolds and of full-dimensional closed regions with C¹ boundary; the same sets
--   - encoding: moduli and talwegs with values in ℝ ∪ {+∞}, sup ∅ = 0 → values in ℝ≥0∞ (ENNReal.ofReal a = a⁺), empty supremum 0; reason: the values are nonnegative; [0, +∞] carries the usual topology of ℝ ∪ {+∞} restricted to it
--   - reading: absolutely continuous on a (possibly non-compact) interval I → absolutely continuous on every compact interval [c, d] ⊆ I (IsLocallyAC); reason: the usual W^{1,1}_loc reading for [t, t+δ), [a, b), (a, b) and the pieces J_i; on a compact interval it is absolute continuity on I
--   - reading: γ̇(t) for t ∈ [a, b), γ defined on [a, b) → any v with HasDerivWithinAt γ v [a, b) t: the derivative at t > a and the right derivative at t = a; reason: the derivative of a curve defined on [a, b); every such t is covered, including t = a
--   - encoding: a curve γ : I → ℝⁿ with −γ̇(t) ∈ N_{S(t)}(γ(t)) for almost every t ∈ I → γ : ℝ → ℝⁿ, and for almost every t ∈ I there is v with HasDerivAt γ v t and −v ∈ N_{S(t)}(γ(t)); reason: values of γ off I play no role; almost every t ∈ I is an interior point of I at which an absolutely continuous curve is differentiable
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Lemma 19, p.13

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_SweepingDesing_IsSmoothSweepingProcess
import Definitions.Def_SweepingDesing_orientedModulus
import Definitions.Def_SweepingDesing_IsACOrbit
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Lemma 19, p.13: let `S` be a smooth sweeping process and `γ ∈ 𝒜𝒞(S, [a, b))`. Then
`‖γ̇(t)‖ = ‖D*S(t, γ(t))|⁺` for all `t ∈ [a, b)` such that `-γ̇(t) ∈ N_{S(t)}(γ(t))` and
`‖D*S(t, γ(t))|⁺` is finite.

**Formalization Note** `γ̇(t)` is the derivative of `γ` as a curve on `[a, b)`: any `v` with
`HasDerivWithinAt γ v [a, b) t` (the two-sided derivative at `t > a`, the right derivative at
`t = a`). The statement covers every such `t`, including `t = a`. -/
theorem lemma_19 {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (hS : IsSmoothSweepingProcess S) (a b : ℝ)
    (γ : ℝ → EuclideanSpace ℝ (Fin n)) (hγ : IsACOrbit S γ (Ico a b)) :
    ∀ t ∈ Ico a b, ∀ v : EuclideanSpace ℝ (Fin n), HasDerivWithinAt γ v (Ico a b) t →
      -v ∈ StrictCQ.CAKKT.limNormal (S t) (γ t) → orientedModulus S t (γ t) ≠ ⊤ →
        ‖v‖ₑ = orientedModulus S t (γ t) := by sorry

end SweepingDesing
