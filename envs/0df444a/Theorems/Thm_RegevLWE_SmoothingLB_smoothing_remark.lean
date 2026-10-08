-- Prove2me | Theorems.Thm_RegevLWE_SmoothingLB_smoothing_remark
-- name    : RegevLWE.SmoothingLB.smoothing_remark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:30.894231+00:00
-- url     : https://prove2.me/theorems/369f74b2-cff1-492a-bb49-f2949f47a347
-- title:
--   Remark after Definition 2.10 — s ↦ ρ_{1/s}(L* ∖ {0}) is continuous and strictly decreasing, and ρ_{1/η_ε(L)}(L* ∖ {0}) = ε
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice of dimension $n \ge 1$ with dual $L^*$, and write $f(s) := \rho_{1/s}(L^*\setminus\{0\}) = \sum_{y \in L^*\setminus\{0\}} e^{-\pi s^2\|y\|^2}$ for $s > 0$. Then
--
--   1. $f$ is continuous on $(0,\infty)$;
--   2. $f$ is strictly decreasing on $(0,\infty)$;
--   3. $f(s) \to \infty$ as $s \to 0^+$;
--   4. $f(s) \to 0$ as $s \to \infty$;
--   5. for every $\epsilon > 0$ the smoothing parameter is positive and is the inverse of $f$ at $\epsilon$:
--   $$\eta_\epsilon(L) > 0, \qquad \rho_{1/\eta_\epsilon(L)}(L^*\setminus\{0\}) = \epsilon .$$
--
--   This makes Definition 2.10 well posed: "the smallest $s$" exists for every $\epsilon > 0$, and the defining inequality holds with equality at $s = \eta_\epsilon(L)$, which is the first step of the proof of Claim 2.13.
--
--   **Formalization Note** The paper's lattices are $n$-dimensional with $n \ge 1$; at $n = 0$ the dual has no nonzero vector and $f \equiv 0$, so the hypothesis $0 < n$ is the paper's standing convention, stated explicitly. "$\epsilon \mapsto \eta_\epsilon(L)$ is the inverse function of $s \mapsto \rho_{1/s}(L^*\setminus\{0\})$" is formalized as item 5 (with item 2, $\eta_\epsilon(L)$ is then the unique $s > 0$ with $f(s) = \epsilon$).
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:19, remark after Definition 2.10

import Mathlib
import Definitions.Def_RegevLWE_SmoothingLB_Lattice

open Filter Topology

namespace RegevLWE.SmoothingLB

theorem smoothing_remark {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ContinuousOn (fun s : ℝ => RegevLWE.GaussConv.rhoDualNonzero (1 / s) L) (Set.Ioi 0) ∧
    StrictAntiOn (fun s : ℝ => RegevLWE.GaussConv.rhoDualNonzero (1 / s) L) (Set.Ioi 0) ∧
    Tendsto (fun s : ℝ => RegevLWE.GaussConv.rhoDualNonzero (1 / s) L) (𝓝[>] 0) atTop ∧
    Tendsto (fun s : ℝ => RegevLWE.GaussConv.rhoDualNonzero (1 / s) L) atTop (𝓝 0) ∧
    ∀ ε : ℝ, 0 < ε →
      0 < RegevLWE.GaussConv.smoothingParam L ε ∧ RegevLWE.GaussConv.rhoDualNonzero (1 / RegevLWE.GaussConv.smoothingParam L ε) L = ε := by sorry

end RegevLWE.SmoothingLB
