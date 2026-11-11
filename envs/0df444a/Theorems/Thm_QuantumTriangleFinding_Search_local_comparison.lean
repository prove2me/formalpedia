-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_local_comparison
-- name    : QuantumTriangleFinding.Search.local_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:29:47.838197+00:00
-- url     : https://prove2.me/theorems/8a2768c7-423a-43c6-944b-7eb285d581e1
-- title:
--   Lemma 5.3 — Local comparison
-- statement:
--   There is an absolute $c>0$ such that the following holds in the local analytic regime for every host triangle $T$, every finite complex workspace and every negative joint vector $f$. The computed four-input map satisfies $T_T|\mu_-\rangle=|\mu_T\rangle$ and
--   $$\|T_Tf\|^2\le c\left(\|f\|^2+\frac1p\sum_{i\in T}\|D_if\|^2\right),\qquad \|T_Tf\|^2\le\frac cp\|f\|^2.$$
--   For $e\notin T$ it commutes with the input phase across the two laws. For $e\in T$,
--   $$(Q_e^+T_T-T_TQ_e^-)f=-2\sum_{i\in T\setminus\{e\}}(f_i^{(T)}-f_0^{(T)}),$$
--   $$\|(Q_e^+T_T-T_TQ_e^-)f\|^2\le\frac cp\sum_{i\in T\setminus\{e\}}\|D_if\|^2.$$
--   The norm on the left uses $\mu_T$ and each norm on the right uses $\mu_-$. The constant precedes all hosts, densities, triangles and workspaces. These are the local properties of the actual four-input map, including the exact signed identity.
--
--   Differences from the source:
--   - generalization: Section 5 assumes Δp ≥ C₀ log(2m), with C₀ sufficiently large → Lemmas 5.3–5.6 assume only Δp ≥ 1 together with 0 < p ≤ 1/(10√Δ) and M ≥ 1; reason: these are the analytic hypotheses used in their proofs; the section chooses C₀ large enough that C₀ log(2m) ≥ 1, so all source instances specialize
--   - encoding: arbitrary finite simple undirected hosts and three-edge triangles → SimpleGraph (Fin N), sorted endpoint pairs and unordered three-vertex cliques; circuits may query every ordered vertex pair; reason: finite relabeling and the vertex-set/edge-set correspondence preserve every instance; loops and host nonedges return zero and both edge orientations agree
--   - encoding: finite complex Hilbert spaces and square-root probability-weighted joint vectors → Euclidean workspaces and support functions with weighted inner products, norms and kernel adjoints; reason: choosing an orthonormal basis and sending f(x) to √ρ(x)f(x) is an isometric change of coordinates; every finite workspace is represented
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Lemma 5.3, (5.10)–(5.13), p. 28

import Definitions.Def_QuantumTriangleFinding_Search_TriangleComparison

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Lemma 5.3, p.28. A single absolute constant works for every host, density and workspace. -/
theorem local_comparison : ∃ c : ℝ, 0 < c ∧
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (p : ℝ), LocalRegime G p →
    ∀ (T : Triangle G),
      (localComparison T p).mulVec (fun _ => 1) = (fun _ => 1) ∧
      (∀ (W : Type) [Fintype W] (f : Joint (negativeLaw G p) W),
        normSq (triangleLaw T p) (applyKernel (localComparison T p) f) ≤
          c * (normSq (negativeLaw G p) f + 1 / p *
            ∑ i ∈ triangleEdges T, normSq (negativeLaw G p)
              (applyKernel (conditionalDifference (negativeLaw G p) i) f)) ∧
        normSq (triangleLaw T p) (applyKernel (localComparison T p) f) ≤
          c / p * normSq (negativeLaw G p) f) ∧
      (∀ e : Edge G, e ∉ triangleEdges T → localQueryError T p e = 0) ∧
      (∀ (W : Type) [Fintype W] (f : Joint (negativeLaw G p) W)
          (e : Edge G), e ∈ triangleEdges T →
        applyKernel (localQueryError T p e) f =
          (-2 : ℂ) • (∑ i ∈ (triangleEdges T).erase e,
            (selectedVector T p {i} f - selectedVector T p ∅ f)) ∧
        normSq (triangleLaw T p) (applyKernel (localQueryError T p e) f) ≤
          c / p * ∑ i ∈ (triangleEdges T).erase e,
            normSq (negativeLaw G p) (applyKernel (conditionalDifference (negativeLaw G p) i) f)) := by sorry

end QuantumTriangleFinding.Search
