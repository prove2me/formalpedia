-- Prove2me | Theorems.Thm_ShorNonsmooth_Decomposition_stochastic_transport_convex
-- name    : ShorNonsmooth.Decomposition.stochastic_transport_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:27:43.703519+00:00
-- url     : https://prove2.me/theorems/43fbc0c5-8611-4d2a-ac5a-711babf4ef8f
-- title:
--   Lemma 4.3 — the stochastic transportation problem is a convex program
-- statement:
--   In the stochastic transportation problem (4.163)–(4.165), let the demands $\xi_j$ have probability densities $p_j$ with finite mean ($\int |z|\, p_j(z)\,dz < \infty$), and let the penalty coefficients satisfy $r_j \ge 0$. Then the problem is a convex programming problem: the feasible set
--   $$
--   \Big\{x = (x_{ij}) : \sum_{j=1}^n x_{ij} \le a_i\ (i = 1,\dots,m),\ x_{ij} \ge 0\Big\}
--   $$
--   is convex, and the objective
--   $$
--   \sum_{i,j} c_{ij} x_{ij} + \sum_{j=1}^n r_j\, E\Big(\xi_j - \sum_{i=1}^m x_{ij}\Big)^+
--   $$
--   is a convex function on it.
--
--   Convexity is what licenses solving the problem through its Lagrangian dual (4.166) by a subgradient-type method, as the book does next.
--
--   **Formalization Note** The book leaves implicit that $r_j \ge 0$ (a penalty coefficient) and that the demands have finite mean (otherwise the expectation is infinite); both are hypotheses. The independence of the $\xi_j$ plays no role in this statement and is not assumed.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 132, Lemma 4.3 (problem (4.163)–(4.165), pp. 131–132)

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_StochasticTransport

namespace ShorNonsmooth.Decomposition

open MeasureTheory

/-- Shor (1985), **Lemma 4.3** (p. 132): the stochastic transportation problem (4.163)–(4.165) is a
convex programming problem — its feasible set is convex and its objective
`Σ c_ij x_ij + Σ r_j E(ξ_j − Σ_i x_ij)⁺` is convex on it. The demands `ξ_j` have probability densities
`p_j` with finite mean (so that the expectations are finite), and the penalty coefficients `r_j` are
nonnegative. -/
theorem stochastic_transport_convex {m n : ℕ}
    (c : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (p : Fin n → ℝ → ℝ) (hp : ∀ j, IsDensity (p j))
    (hmean : ∀ j, Integrable (fun z => z * p j z)) :
    Convex ℝ (stochTransportFeasible (n := n) a) ∧
      ConvexOn ℝ (stochTransportFeasible a) (stochTransportObjective c r p) := by sorry

end ShorNonsmooth.Decomposition
