-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_two_triangle_sums
-- name    : QuantumTriangleFinding.Search.two_triangle_sums
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:29:39.846767+00:00
-- url     : https://prove2.me/theorems/1d88be15-258b-4aaa-8b4d-51e41ff7b767
-- title:
--   Lemma 5.5 — Two triangle sums
-- statement:
--   In the local analytic regime fix a queried host edge $e=uv$, and set $A_e=\{T:e\in T\}$ and $B_{u,v}=\{T:u\in V(T),v\notin V(T)\}$. There is an absolute $c>0$, independent of the host, density, workspace and query, such that for every negative joint vector $f$ and $R\ge1$,
--   $$\sum_{T\in A_e}\sum_{i\in T\setminus\{e\}}\|D_iF_Tf\|^2\le c\left(R+\frac{\Delta p}R\right)\|f\|^2+c\left(\Delta b+\frac{\Delta\tau^2}{R^2}\right)\|f\|_\infty^2,$$
--   $$\sum_{T\in B_{u,v}}\sum_{i\in T}\|D_iF_Tf\|^2\le c\left(\Delta R+\frac{\Delta^2p}R\right)\|f\|^2+c\left(\Delta^2b+\frac{\Delta^2\tau^2}{R^2}\right)\|f\|_\infty^2.$$
--   Both endpoint orientations are quantified. All incidence multiplicities are counted, without any disjoint-triangle restriction. The quantities $b$ and $\tau^2$ are the computed degree-tail quantities, and every norm uses $\mu_-$.
--
--   Differences from the source:
--   - generalization: Section 5 assumes Δp ≥ C₀ log(2m), with C₀ sufficiently large → Lemmas 5.3–5.6 assume only Δp ≥ 1 together with 0 < p ≤ 1/(10√Δ) and M ≥ 1; reason: these are the analytic hypotheses used in their proofs; the section chooses C₀ large enough that C₀ log(2m) ≥ 1, so all source instances specialize
--   - encoding: arbitrary finite simple undirected hosts and three-edge triangles → SimpleGraph (Fin N), sorted endpoint pairs and unordered three-vertex cliques; circuits may query every ordered vertex pair; reason: finite relabeling and the vertex-set/edge-set correspondence preserve every instance; loops and host nonedges return zero and both edge orientations agree
--   - encoding: finite complex Hilbert spaces and square-root probability-weighted joint vectors → Euclidean workspaces and support functions with weighted inner products, norms and kernel adjoints; reason: choosing an orthonormal basis and sending f(x) to √ρ(x)f(x) is an isometric change of coordinates; every finite workspace is represented
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Lemma 5.5, (5.21)–(5.22), p. 31

import Definitions.Def_QuantumTriangleFinding_Search_TriangleComparison

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Lemma 5.5, p.31: both incidence sums, for either orientation of the queried edge. -/
theorem two_triangle_sums : ∃ c : ℝ, 0 < c ∧
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (p : ℝ), LocalRegime G p →
    ∀ (R : ℝ), 1 ≤ R → ∀ (W : Type) [Fintype W]
      (f : Joint (negativeLaw G p) W) (e : Edge G) (u v : Fin N),
      (e.val = (u, v) ∨ e.val = (v, u)) →
    let μ := negativeLaw G p
    let Δ : ℝ := maxDegree G
    ((∑ T ∈ Finset.univ.filter (fun T : Triangle G => e ∈ triangleEdges T),
      ∑ i ∈ (triangleEdges T).erase e,
        normSq μ (applyKernel (conditionalDifference μ i) (applyKernel (triangleAverage T p R) f))) ≤
      c * (R + Δ * p / R) * normSq μ f +
      c * (Δ * tailBound G p + Δ * tauSq G p / R ^ 2) * infinityNorm μ f ^ 2) ∧
    ((∑ T ∈ Finset.univ.filter (fun T : Triangle G => u ∈ T.val ∧ v ∉ T.val),
      ∑ i ∈ triangleEdges T,
        normSq μ (applyKernel (conditionalDifference μ i) (applyKernel (triangleAverage T p R) f))) ≤
      c * (Δ * R + Δ ^ 2 * p / R) * normSq μ f +
      c * (Δ ^ 2 * tailBound G p + Δ ^ 2 * tauSq G p / R ^ 2) * infinityNorm μ f ^ 2) := by sorry

end QuantumTriangleFinding.Search
