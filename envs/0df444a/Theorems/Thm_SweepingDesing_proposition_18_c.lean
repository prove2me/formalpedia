-- Prove2me | Theorems.Thm_SweepingDesing_proposition_18_c
-- name    : SweepingDesing.proposition_18_c
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:22.981995+00:00
-- url     : https://prove2.me/theorems/6e58de6c-5533-4108-8a77-e88659dd6855
-- title:
--   Proposition 18 c) — an inward-in-time normal ray keeps the point in $S(t)$
-- statement:
--   Let $S:\mathbb R\rightrightarrows\mathbb R^n$ be a smooth sweeping process with graph $\mathcal S$, let $T=\sup\operatorname{dom}(S)$, fix $\bar t\in\operatorname{dom}(S)\setminus\{T\}$ and $\bar x\in S(\bar t)$. If $\operatorname{int}(\mathcal S)\neq\emptyset$ and $N_{\mathcal S}(\bar t,\bar x)=\mathbb R_+(\alpha,u)$ for some $(\alpha,u)$ with $\alpha<0$, then there is $\delta>0$ such that
--
--   $$
--   \bar x\in S(t)\qquad\text{for all }t\in[\bar t,\bar t+\delta).
--   $$
--
--   It is used in the proof of Lemma 19.
--
--   Differences from the source:
--   - encoding: smooth sweeping process (Definition 10): a closed connected C¹ submanifold of ℝⁿ⁺¹ of dimension at most n, or a connected full-dimensional manifold with boundary whose boundary is a C¹ manifold of dimension n (closed graph, §3.1) → IsSmoothSweepingProcess: the graph is closed and connected and is cut out near each of its points by a C¹ submersion onto ℝ^{n+1−k} with one k ≤ n, or near each of its frontier points by {g ≤ 0} with g C¹ and dg ≠ 0; reason: the standard local description of C¹ embedded submanifolds and of full-dimensional closed regions with C¹ boundary; the same sets
--   - encoding: t̄ ∈ dom(S) with t̄ < T = sup dom(S) (resp. t̄ ∈ dom(S) ∖ {T}) → S(t̄) ≠ ∅ and S(s) ≠ ∅ for some s > t̄; reason: T may be +∞; for t̄ ∈ dom(S) these are the same condition
--   - encoding: ℝⁿ⁺¹ with its Euclidean norm, time first → ℝ × EuclideanSpace ℝ (Fin n) with the max of the two norms; reason: normal cones, ∂𝒮 and Pompeiu–Hausdorff continuity do not change under an equivalent norm
--   - encoding: N_𝒮(t̄, x̄) = ℝ₊(α, u) → the limiting normal cone equals {s • (α, u) : s ≥ 0} for some α < 0 and u; reason: ℝ₊ = [0, ∞); a set equality as printed
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Proposition 18 c), p.12

import Mathlib
import Definitions.Def_SweepingDesing_IsSmoothSweepingProcess
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Proposition 18 c), p.12 (geometric facts): let `S` be a smooth sweeping process, fix
`t̄ ∈ dom(S) ∖ {T}` and `x̄ ∈ S(t̄)`. If `int(𝒮)` is nonempty and `N_𝒮(t̄, x̄) = ℝ₊(α, u)` with
`α < 0`, then there is `δ > 0` such that `x̄ ∈ S(t)` for all `t ∈ [t̄, t̄ + δ)`.

**Formalization Note** `ℝ₊(α, u) = {s • (α, u) : s ≥ 0}`, a set equality with the limiting
normal cone of `𝒮 = gph S` at `(t̄, x̄)`. -/
theorem proposition_18_c {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (hS : IsSmoothSweepingProcess S)
    (tbar : ℝ) (hT : ∃ s, tbar < s ∧ (S s).Nonempty) (xbar : EuclideanSpace ℝ (Fin n)) (hx : xbar ∈ S tbar)
    (hint : (interior (GenNewtonSubgrad.ProxReg.gph S)).Nonempty)
    (hray : ∃ α : ℝ, ∃ u : EuclideanSpace ℝ (Fin n), α < 0 ∧
      GenNewtonSubgrad.ProxReg.limNormal (GenNewtonSubgrad.ProxReg.gph S) (tbar, xbar) =
        {p | ∃ s : ℝ, 0 ≤ s ∧ p = s • (α, u)}) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Ico tbar (tbar + δ), xbar ∈ S t := by sorry

end SweepingDesing
