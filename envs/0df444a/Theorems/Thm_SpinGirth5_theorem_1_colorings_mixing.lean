-- Prove2me | Theorems.Thm_SpinGirth5_theorem_1_colorings_mixing
-- name    : SpinGirth5.theorem_1_colorings_mixing
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:10:34.455207+00:00
-- url     : https://prove2.me/theorems/90a415fc-f784-47ea-92f6-6ad75514163e
-- title:
--   Theorem 1 — Glauber dynamics for proper $q$-colourings of girth-5 graphs mixes in $O(n^2\log q/\delta)$ steps when $q\ge(1+\delta)\Delta$
-- statement:
--   There is an absolute constant $C>0$ such that for every $0<\delta<1$ there exists $\Delta_0(\delta)>0$ with the following property. For every $n$-vertex graph $G$ with maximum degree $\Delta\ge\Delta_0(\delta)$ and girth at least $5$, and every integer $q\ge(1+\delta)\Delta$, the heat-bath Glauber dynamics on proper $q$-colourings — choose a vertex $v$ uniformly and recolour it uniformly from $[q]\setminus\{\chi_t(u):u\sim v\}$ — satisfies
--   $$\max_{\chi_0}\big\|P^t(\chi_0,\cdot)-\pi\big\|_{\mathrm{TV}}\le\frac14\qquad\text{for every } t\ge C\,\frac{n^2}{\delta}\log q,$$
--   where $\pi$ is the uniform distribution on proper $q$-colourings. That is, the mixing time is $O\big(\frac{n^2}{\delta}\log q\big)$.
--
--   This brings rapid mixing of the Glauber dynamics for colourings with $q\ge(1+\delta)\Delta$ down to girth $5$, from girth $7$ in earlier work.
--
--   **Formalization Note** The chain is the published `MarkovMixing.coloringGlauber G q` with stationary law `MarkovMixing.uniformDist` on proper colourings; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: mixing time O(n²/δ · log q) → an absolute C > 0 quantified before δ, and max_x ‖P^t(x,·) − π‖_TV ≤ 1/4 for every t ≥ C n² log q/δ; reason: t_mix(1/4) ≤ ⌈C n² log q/δ⌉ is equivalent since the worst-start distance is nonincreasing in t; the published mixingTime is an sInf with junk value 0 on ∅
--   - encoding: the heat-bath Glauber dynamics and uniform measure over proper q-colorings → MarkovMixing.coloringGlauber G q and MarkovMixing.uniformDist on proper colourings; reason: coloringGlauber resamples v from the uniform law on proper colourings conditioned off v, i.e. uniformly among the colours absent from N(v)
--   - encoding: girth at least 5 (∞ for a forest) → 5 ≤ G.egirth; reason: Mathlib's egirth is ⊤ for acyclic graphs, so forests are included
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Theorem 1, p.3

import Mathlib
import Definitions.Def_mm_transport

namespace SpinGirth5

/-- **Theorem 1** (proper colourings). There is an absolute constant `C > 0` such that for every
`0 < δ < 1` there is `Δ₀(δ) > 0` with the following property: for every `n`-vertex graph with
maximum degree `Δ ≥ Δ₀(δ)` and girth at least 5, and every integer `q ≥ (1 + δ)Δ`, the heat-bath
Glauber dynamics on proper `q`-colourings is within total variation distance `1/4` of the
uniform distribution from every start after any `t ≥ C n² log q / δ` steps; that is, its mixing
time is `O(n²/δ · log q)`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Theorem 1, p.3 (the chain and the mixing time are defined on p.3).

**Formalization Note** The chain is the published `MarkovMixing.coloringGlauber G q`: pick a
uniform vertex and recolour it from the uniform law on proper colourings conditioned off that
vertex, i.e. uniformly among the colours absent from its neighbourhood. Its stationary law is
`MarkovMixing.uniformDist` on proper colourings. `O(·)` is an absolute constant `C`, quantified
before `δ`; the bound is stated through `MarkovMixing.distStationary` (`max_x ‖P^t(x,·) − π‖_TV`)
for every `t ≥ C n² log q/δ`, which says `t_mix(1/4) ≤ ⌈C n² log q/δ⌉`. Girth at least 5 is
`5 ≤ G.egirth`, so forests are included; `Δ = G.maxDegree`; `log` is the natural logarithm. -/
theorem theorem_1_colorings_mixing :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ Δ₀ : ℕ, 0 < Δ₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Δ₀ ≤ G.maxDegree → 5 ≤ G.egirth →
        ∀ q : ℕ, (1 + δ) * (G.maxDegree : ℝ) ≤ q →
        ∀ t : ℕ, C * (Fintype.card V : ℝ) ^ 2 * Real.log q / δ ≤ t →
          MarkovMixing.distStationary (MarkovMixing.coloringGlauber G q)
            (MarkovMixing.uniformDist {c : V → Fin q // MarkovMixing.IsProperColoring G c}) t ≤
            1 / 4 := by sorry

end SpinGirth5
