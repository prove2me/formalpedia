-- Prove2me | Theorems.Thm_RiskAverseConsistency_theorem_4
-- name    : RiskAverseConsistency.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:29.131198+00:00
-- url     : https://prove2.me/theorems/2de1e9e5-a2f4-44cb-bd74-99ea6a9aa9fc
-- title:
--   Theorem 4 — consistency of approximate minimizers under Mosco-epiconvergence
-- statement:
--   Let $V$ be a reflexive Banach space and $V_0\subset V$ a closed, nonempty, convex set. Suppose $h_k:V_0\to(-\infty,\infty]$ Mosco-epiconverges to $h:V_0\to(-\infty,\infty]$. Let $(v_k)\subset V_0$ and $(\varepsilon_k)\subset[0,\infty)$ with $\varepsilon_k\to0^+$ and
--
--   $$
--   h_k(v_k)\le\inf_{v\in V_0}h_k(v)+\varepsilon_k\qquad\text{for each }k .
--   $$
--
--   If $(v_k)_K$ is a subsequence with $v_k\rightharpoonup\bar v$ as $K\ni k\to\infty$, then
--
--   1. $\bar v\in V_0$,
--   2. $h(\bar v)=\inf_{v\in V_0}h(v)$,
--   3. $\inf_{v\in V_0}h_k(v)\to\inf_{v\in V_0}h(v)$ as $K\ni k\to\infty$,
--   4. $h_k(v_k)\to h(\bar v)$ as $K\ni k\to\infty$.
--
--   This is the abstract consistency principle on which the analysis of the empirical approximation rests: weak cluster points of approximate minimizers are minimizers of the limit, and optimal values converge.
--
--   Differences from the source:
--   - encoding: functions with values in (−∞, ∞] → EReal-valued functions with the value ⊥ = −∞ excluded on the domain set; reason: Lean convention; same instances
--   - encoding: functions defined on the subset (V₀, Z_ad, Y₀) → functions on the ambient space whose values off the subset are never used; reason: Lean convention; every quantifier is restricted to the subset, so no instance changes
--   - encoding: subsequence (v_k)_K, K ∋ k → ∞ → v ∘ K with K : ℕ → ℕ strictly increasing; reason: Lean convention; same subsequences
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, pp.5–6, Theorem 4

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_RiskAverseConsistency_MoscoConvergesOn
import Definitions.Def_RiskAverseConsistency_optimalValue

open Filter Topology QuasiHemiVI.Existence

namespace RiskAverseConsistency

/-- **Theorem 4** (consistency under Mosco-epiconvergence). Let `V` be a reflexive Banach space and
`V₀ ⊂ V` closed, nonempty and convex. Suppose `hₖ : V₀ → (−∞, ∞]` Mosco-epiconverges to
`h : V₀ → (−∞, ∞]`. Let `(vₖ) ⊂ V₀` and `(εₖ) ⊂ [0, ∞)` with `εₖ → 0⁺` and
`hₖ(vₖ) ≤ inf_{v ∈ V₀} hₖ(v) + εₖ` for each `k`. If `(vₖ)_K` is a subsequence with `vₖ ⇀ v̄` as
`K ∋ k → ∞`, then (1) `v̄ ∈ V₀`, (2) `h(v̄) = inf_{V₀} h`, (3) `inf_{V₀} hₖ → inf_{V₀} h` and
(4) `hₖ(vₖ) → h(v̄)` as `K ∋ k → ∞`.

Milz, Surowiec, arXiv:2207.14756v2, Theorem 4, pp.5–6.

Formalization Note: `(−∞, ∞]`-valued functions are `EReal`-valued with the value `⊥ = −∞` excluded
on `V₀`. The subsequence `(vₖ)_K` is `v ∘ K` with `K` strictly increasing. Infima are in `EReal`
(`optimalValue`). -/
theorem theorem_4 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (hV : IsReflexive V) {V₀ : Set V} (hV₀_closed : IsClosed V₀) (hV₀_ne : V₀.Nonempty)
    (hV₀_convex : Convex ℝ V₀) (h : ℕ → V → EReal) (hlim : V → EReal)
    (h_ne_bot : ∀ k, ∀ v ∈ V₀, h k v ≠ ⊥) (hlim_ne_bot : ∀ v ∈ V₀, hlim v ≠ ⊥)
    (hMosco : MoscoConvergesOn V₀ h hlim) (v : ℕ → V) (hv : ∀ k, v k ∈ V₀) (ε : ℕ → ℝ)
    (hε_nonneg : ∀ k, 0 ≤ ε k) (hε : Tendsto ε atTop (𝓝 0))
    (hmin : ∀ k, h k (v k) ≤ optimalValue V₀ (h k) + (ε k : EReal))
    (K : ℕ → ℕ) (hK : StrictMono K) (vbar : V) (hweak : WeakConv (fun j => v (K j)) vbar) :
    vbar ∈ V₀ ∧ hlim vbar = optimalValue V₀ hlim ∧
      Tendsto (fun j => optimalValue V₀ (h (K j))) atTop (𝓝 (optimalValue V₀ hlim)) ∧
      Tendsto (fun j => h (K j) (v (K j))) atTop (𝓝 (hlim vbar)) := by sorry

end RiskAverseConsistency
