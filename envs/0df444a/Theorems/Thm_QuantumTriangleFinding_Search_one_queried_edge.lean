-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_one_queried_edge
-- name    : QuantumTriangleFinding.Search.one_queried_edge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:29:55.599958+00:00
-- url     : https://prove2.me/theorems/048c6577-b2bc-470c-b772-2e76194d3247
-- title:
--   Lemma 5.6 — One queried edge
-- statement:
--   There is an absolute $c>0$ such that, in the local analytic regime, for every $R\ge1$ there exist $\alpha,\beta\ge0$, depending only on $G,p,R$, with the following properties. For the actual comparison map $\Upsilon_R$ from (5.25), every edge $e$, every finite workspace and every negative joint vector $f$ satisfy
--   $$\|(Q_e^+\Upsilon_R-\Upsilon_RQ_e^-)f\|^2\le\alpha\|f\|^2+\beta\|f\|_\infty^2,$$
--   $$\alpha\le\frac cM\left(\frac Rp+\frac\Delta R+\frac\Delta{R^2}+\frac{\Delta^2p}{R^2}\right),$$
--   $$\beta\le\frac cM\left(\frac{\Delta b}p+\frac{\Delta\tau^2}{pR^2}+\frac{\Delta^2b}{R^2}+\frac{\Delta^2\tau^2}{pR^4}\right).$$
--   The left norm uses $\mu_+$ and the right norms use $\mu_-$. The same $\alpha,\beta$ work for every queried edge and workspace. All four terms in each coefficient bound are retained, including the factor $1/p$ in the final rare-input term.
--
--   Differences from the source:
--   - generalization: Section 5 assumes Δp ≥ C₀ log(2m), with C₀ sufficiently large → Lemmas 5.3–5.6 assume only Δp ≥ 1 together with 0 < p ≤ 1/(10√Δ) and M ≥ 1; reason: these are the analytic hypotheses used in their proofs; the section chooses C₀ large enough that C₀ log(2m) ≥ 1, so all source instances specialize
--   - encoding: arbitrary finite simple undirected hosts and three-edge triangles → SimpleGraph (Fin N), sorted endpoint pairs and unordered three-vertex cliques; circuits may query every ordered vertex pair; reason: finite relabeling and the vertex-set/edge-set correspondence preserve every instance; loops and host nonedges return zero and both edge orientations agree
--   - encoding: finite complex Hilbert spaces and square-root probability-weighted joint vectors → Euclidean workspaces and support functions with weighted inner products, norms and kernel adjoints; reason: choosing an orthonormal basis and sending f(x) to √ρ(x)f(x) is an isometric change of coordinates; every finite workspace is represented
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Lemma 5.6, (5.27)–(5.29), p. 32; comparison map (5.25), p. 31

import Definitions.Def_QuantumTriangleFinding_Search_TriangleComparison

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Lemma 5.6, p.32: α,β depend on G,p,R, but never on the edge, workspace or vector. -/
theorem one_queried_edge : ∃ c : ℝ, 0 < c ∧
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (p : ℝ), LocalRegime G p →
    ∀ (R : ℝ), 1 ≤ R → ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      (α ≤ c / (triangleCount G : ℝ) *
        (R / p + (maxDegree G : ℝ) / R + (maxDegree G : ℝ) / R ^ 2 +
          (maxDegree G : ℝ) ^ 2 * p / R ^ 2)) ∧
      (β ≤ c / (triangleCount G : ℝ) *
        ((maxDegree G : ℝ) * tailBound G p / p +
          (maxDegree G : ℝ) * tauSq G p / (p * R ^ 2) +
          (maxDegree G : ℝ) ^ 2 * tailBound G p / R ^ 2 +
          (maxDegree G : ℝ) ^ 2 * tauSq G p / (p * R ^ 4))) ∧
      (∀ (e : Edge G) (W : Type) [Fintype W] (f : Joint (negativeLaw G p) W),
        normSq (positiveLaw G p) (applyKernel (transferQueryError G p R e) f) ≤
          α * normSq (negativeLaw G p) f + β * infinityNorm (negativeLaw G p) f ^ 2) := by sorry

end QuantumTriangleFinding.Search
