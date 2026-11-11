-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_star_averages
-- name    : QuantumTriangleFinding.Search.star_averages
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:45.512482+00:00
-- url     : https://prove2.me/theorems/5475724a-92c4-4d11-99ce-a2da3fb0c2d4
-- title:
--   Lemma 5.4 — Bounds for star averages
-- statement:
--   In the local analytic regime let $\mu=\mu_-$, and use the computed $b$ and $\tau^2=144p^2\Delta^2b$. For every negative joint vector $f$ in every finite workspace, every vertex $w$ and every $R>0$,
--   $$\sum_{i\in\mathrm{st}(w)}\langle D_if,F_wD_if\rangle\le3R\|f\|^2+\Delta b\|f\|_\infty^2.$$
--   For every host triangle $T$, every edge coordinate $i$ and every $R\ge1$,
--   $$\|D_iF_Tf\|^2\le4\|F_TD_if\|^2+\frac pR\|f\|^2+\frac{4\tau^2}{R^2}\|f\|_\infty^2.$$
--   All norms use $\mu_-$. The two ranges of $R$ remain distinct. The star and triangle averages are the actual resolvents of the conditional differences, and the rare-input quantities are not free parameters. These are both estimates used in the subsequent triangle sums.
--
--   Differences from the source:
--   - generalization: Section 5 assumes Δp ≥ C₀ log(2m), with C₀ sufficiently large → Lemmas 5.3–5.6 assume only Δp ≥ 1 together with 0 < p ≤ 1/(10√Δ) and M ≥ 1; reason: these are the analytic hypotheses used in their proofs; the section chooses C₀ large enough that C₀ log(2m) ≥ 1, so all source instances specialize
--   - encoding: arbitrary finite simple undirected hosts and three-edge triangles → SimpleGraph (Fin N), sorted endpoint pairs and unordered three-vertex cliques; circuits may query every ordered vertex pair; reason: finite relabeling and the vertex-set/edge-set correspondence preserve every instance; loops and host nonedges return zero and both edge orientations agree
--   - encoding: finite complex Hilbert spaces and square-root probability-weighted joint vectors → Euclidean workspaces and support functions with weighted inner products, norms and kernel adjoints; reason: choosing an orthonormal basis and sending f(x) to √ρ(x)f(x) is an isometric change of coordinates; every finite workspace is represented
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Lemma 5.4, (5.18)–(5.19), p. 29; tail definitions (5.16)–(5.17), p. 29

import Definitions.Def_QuantumTriangleFinding_Search_TriangleComparison

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Lemma 5.4, p.29: both R ranges, with the computed b and τ². -/
theorem star_averages {N : ℕ} (G : SimpleGraph (Fin N)) (p : ℝ) (h : LocalRegime G p)
    {W : Type} [Fintype W] (f : Joint (negativeLaw G p) W) :
    (∀ (w : Fin N) (R : ℝ), 0 < R →
      (∑ i ∈ starEdges G w,
        (jointInner (negativeLaw G p) (applyKernel (conditionalDifference (negativeLaw G p) i) f)
          (applyKernel (starAverage G p R w)
            (applyKernel (conditionalDifference (negativeLaw G p) i) f))).re) ≤
        3 * R * normSq (negativeLaw G p) f +
          (maxDegree G : ℝ) * tailBound G p * infinityNorm (negativeLaw G p) f ^ 2) ∧
    (∀ (T : Triangle G) (i : Edge G) (R : ℝ), 1 ≤ R →
      normSq (negativeLaw G p) (applyKernel (conditionalDifference (negativeLaw G p) i)
        (applyKernel (triangleAverage T p R) f)) ≤
      4 * normSq (negativeLaw G p) (applyKernel (triangleAverage T p R)
        (applyKernel (conditionalDifference (negativeLaw G p) i) f)) +
      p / R * normSq (negativeLaw G p) f +
      4 * tauSq G p / R ^ 2 * infinityNorm (negativeLaw G p) f ^ 2) := by sorry

end QuantumTriangleFinding.Search
