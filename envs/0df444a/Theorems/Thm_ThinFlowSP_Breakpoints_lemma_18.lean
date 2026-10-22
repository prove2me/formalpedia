-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_lemma_18
-- name    : ThinFlowSP.Breakpoints.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:35.973105+00:00
-- url     : https://prove2.me/theorems/6203f6e6-5bcb-4f39-9842-0837885fb560
-- title:
--   Lemma 18, p. 12 — scaling of parametric thin flows; ϱ^{G′}_v non-decreasing, ϱ^{G′}_v(ν′₀)/ν′₀ non-increasing
-- statement:
--   Let $G' = (V, A', A^*)$ be a shortest path graph with resetting with $s \ne t$ and $\nu \in \mathbb R^{A'}_{>0}$ capacities, and let $(\varrho^{G'}, \chi^{G'})$ be as in Proposition 17.
--
--   1. For all $\nu'_0 \ge 0$ and $\ell'_0 > 0$, the vector $\ell'_0\cdot\chi^{G'}(\nu'_0/\ell'_0)$ is a normalized thin $s$–$t$-flow with resetting of value $\nu'_0$ and $\ell'_0\cdot\varrho^{G'}(\nu'_0/\ell'_0)$ are corresponding labels.
--   2. For every $v \in V$, the function $\nu'_0 \mapsto \varrho^{G'}_v(\nu'_0)$ is non-decreasing on $[0,\infty)$ and
--   $$\nu'_0 \mapsto \frac{1}{\nu'_0}\,\varrho^{G'}_v(\nu'_0)$$
--   is non-increasing on $(0,\infty)$.
--
--   These scaling and monotonicity facts drive the series and parallel composition lemmas (Lemmas 29 and 30).
--
--   **Formalization Note** Part 1 is stated for every pair $(\varrho, \chi)$ with the property of Proposition 17 and part 2 for every label function; by Corollary 15 these are statements about $\varrho^{G'}$. The page says "$\ell'_0 \ge 0$", but at $\ell'_0 = 0$ the expression $\nu'_0/\ell'_0$ is undefined and the claim fails for $\nu'_0 > 0$ (the scaled flow has value $0$); the statement uses $\ell'_0 > 0$. The page omits the capacities, which are added as in every other statement of §4, as is the standing assumption $s \ne t$.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 12, Lemma 18

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem lemma_18 (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t) (hν : ∀ a, 0 < ν a) :
    (∀ (ρ : ℝ → G.V → ℝ) (χ : ℝ → G.A → ℝ), IsParametricThinFlow G Astar ν ρ χ →
      ∀ nu0 l0 : ℝ, 0 ≤ nu0 → 0 < l0 →
        IsStaticFlow G (l0 • χ (nu0 / l0)) nu0 ∧
        IsThinFlowLabels G Astar ν (l0 • χ (nu0 / l0)) (l0 • ρ (nu0 / l0))) ∧
    (∀ ρ : ℝ → G.V → ℝ, IsLabelFunction G Astar ν ρ → ∀ v,
      MonotoneOn (fun r => ρ r v) (Set.Ici 0) ∧
      AntitoneOn (fun r => ρ r v / r) (Set.Ioi 0)) := by sorry

end ThinFlowSP.Breakpoints
