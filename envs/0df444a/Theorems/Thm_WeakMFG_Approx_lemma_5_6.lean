-- Prove2me | Theorems.Thm_WeakMFG_Approx_lemma_5_6
-- name    : WeakMFG.Approx.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:22.845987+00:00
-- url     : https://prove2.me/theorems/43cd31c4-321d-46ad-9d70-f27ec088778c
-- title:
--   Lemma 5.6 — joint continuity at $\{x_0\}\times K$ for compact $K$ via the uniform deviation
-- statement:
--   Let $E$ and $K$ be topological spaces with $K$ compact, let $G:E\times K\to\mathbb R$ and fix $x_0\in E$. Then $G$ is jointly continuous at every point of $\{x_0\}\times K$ if and only if $G(x_0,\cdot)$ is continuous on $K$ and the map
--   $$x\longmapsto\sup_{y\in K}\big|G(x,y)-G(x_0,y)\big|$$
--   is continuous at $x_0$.
--
--   The paper uses this criterion to transfer continuity in the measure argument of $f$ to continuity of a supremum over the compact set $A\times\mathcal P(A)$ in the proof of Lemma 8.2.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$, so it is the true supremum also when $G(x,\cdot)$ is unbounded; since it vanishes at $x_0$, continuity at $x_0$ means convergence to $0$ as $x\to x_0$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Lemma 5.6, p. 16

import Mathlib

open Filter Topology
open scoped ENNReal

namespace WeakMFG.Approx

/-- Lemma 5.6 (Carmona–Lacker, arXiv:1307.1152v2, p. 16). Let `E` and `K` be topological spaces
with `K` compact, `G : E × K → ℝ`, `x₀ ∈ E`. Then `G` is jointly continuous at the points of
`{x₀} × K` iff `G(x₀, ·)` is continuous and `x ↦ sup_{y ∈ K} |G(x, y) − G(x₀, y)|` is continuous at
`x₀`.
Formalization Note: the supremum is taken in `ℝ≥0∞` (a real `⨆` would be `0` when unbounded); it
vanishes at `x₀`, so its continuity at `x₀` is convergence to `0` as `x → x₀`. -/
theorem lemma_5_6 {E K : Type*} [TopologicalSpace E] [TopologicalSpace K] [CompactSpace K]
    (G : E × K → ℝ) (x₀ : E) :
    (∀ y : K, ContinuousAt G (x₀, y)) ↔
      (Continuous (fun y : K => G (x₀, y)) ∧
        Tendsto (fun x : E => ⨆ y : K, ENNReal.ofReal |G (x, y) - G (x₀, y)|) (𝓝 x₀) (𝓝 0)) := by sorry

end WeakMFG.Approx
