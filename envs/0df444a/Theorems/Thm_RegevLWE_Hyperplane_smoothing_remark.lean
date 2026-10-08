-- Prove2me | Theorems.Thm_RegevLWE_Hyperplane_smoothing_remark
-- name    : RegevLWE.Hyperplane.smoothing_remark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:44.724596+00:00
-- url     : https://prove2.me/theorems/c915c1ea-c97b-4b6c-aa60-2dac0a6cdb85
-- title:
--   Remark after Definition 2.10 — s ↦ ρ_{1/s}(L* ∖ {0}) is continuous, strictly decreasing, from ∞ to 0, and η_ε(L) is its inverse
-- statement:
--   Let $n \ge 1$ and let $L \subset \mathbb{R}^n$ be a lattice with dual $L^*$. Consider the function
--   $$f(s) := \rho_{1/s}(L^* \setminus \{0\}) = \sum_{y \in L^*,\, y \neq 0} e^{-\pi s^2 \|y\|^2}, \qquad s > 0 .$$
--   Then:
--
--   1. $f$ is continuous on $(0, \infty)$;
--   2. $f$ is strictly decreasing on $(0, \infty)$;
--   3. $f(s) \to \infty$ as $s \to 0^+$;
--   4. $f(s) \to 0$ as $s \to \infty$;
--   5. for every $\epsilon > 0$, the smoothing parameter $\eta_\epsilon(L)$ is positive and $f(\eta_\epsilon(L)) = \epsilon$, i.e. $\epsilon \mapsto \eta_\epsilon(L)$ is the inverse function of $f$.
--
--   In particular the smoothing parameter of Definition 2.10 is well defined (the infimum is attained) for every $\epsilon > 0$.
--
--   **Formalization Note** The hypothesis $n \ge 1$ is added: for $n = 0$ the set $L^* \setminus \{0\}$ is empty, $f \equiv 0$, and items 2, 3 and 5 fail. The paper's lattices are $n$-dimensional with $n \ge 1$. $\eta_\epsilon(L)$ is the infimum of Definition 2.10 as defined in this mission.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:19, paragraph after Definition 2.10

import Mathlib
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian

open Filter Topology

namespace RegevLWE.Hyperplane

theorem smoothing_remark {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ContinuousOn (fun s : ℝ => RegevLWE.GaussConv.rhoDualNonzero (1 / s) L) (Set.Ioi 0) ∧
    StrictAntiOn (fun s : ℝ => RegevLWE.GaussConv.rhoDualNonzero (1 / s) L) (Set.Ioi 0) ∧
    Tendsto (fun s : ℝ => RegevLWE.GaussConv.rhoDualNonzero (1 / s) L) (𝓝[>] 0) atTop ∧
    Tendsto (fun s : ℝ => RegevLWE.GaussConv.rhoDualNonzero (1 / s) L) atTop (𝓝 0) ∧
    ∀ ε : ℝ, 0 < ε →
      0 < RegevLWE.GaussConv.smoothingParam L ε ∧ RegevLWE.GaussConv.rhoDualNonzero (1 / RegevLWE.GaussConv.smoothingParam L ε) L = ε := by sorry

end RegevLWE.Hyperplane
