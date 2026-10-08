-- Prove2me | Theorems.Thm_RegevLWE_GaussConv_pointwise_bound
-- name    : RegevLWE.GaussConv.pointwise_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:17.014981+00:00
-- url     : https://prove2.me/theorems/16bde345-62b5-488e-be84-6dae5649eaef
-- title:
--   Proof of Claim 3.9, p. 34:26 — pointwise density bound |Y(x) − ρ_t(x)/tⁿ| ≤ ρ_t(x)/tⁿ · 4ε
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice, $u \in \mathbb{R}^n$, $r, s > 0$, $t := \sqrt{r^2 + s^2}$, and $0 < \epsilon < \tfrac12$ with
--   $$\frac{rs}{t} \ge \eta_\epsilon(L).$$
--   Let $Y(x) = \sum_{y \in L+u} D_{L+u,r}(y)\,\nu_s(x - y)$ be the density of a sample of $D_{L+u,r}$ plus independent $\nu_s$ noise. Then for every $x \in \mathbb{R}^n$,
--   $$\Bigl| Y(x) - \frac{\rho_t(x)}{t^n} \Bigr| \le \frac{\rho_t(x)}{t^n}\cdot 4\epsilon .$$
--
--   The density of $Y$ is within a relative error $4\epsilon$ of the continuous Gaussian density $\nu_t = \rho_t/t^n$ at every point; integrating over $\mathbb{R}^n$ gives Claim 3.9.
--
--   **Formalization Note** $\epsilon > 0$ is added (Definition 2.10 defines $\eta_\epsilon$ only for $\epsilon > 0$; for $\epsilon \le 0$ the infimum in the definition is over the empty set and the hypothesis would be vacuous). $\eta_\epsilon(L)$ is the infimum of Definition 2.10.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:26, proof of Claim 3.9, display before 'We complete the proof by integrating over ℝⁿ'

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice

namespace RegevLWE.GaussConv

theorem pointwise_bound {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    [IsZLattice ℝ L] (u : EuclideanSpace ℝ (Fin n)) {r s ε : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (h : smoothingParam L ε ≤ r * s / Real.sqrt (r ^ 2 + s ^ 2))
    (x : EuclideanSpace ℝ (Fin n)) :
    |Ydensity L u r s x - rho (Real.sqrt (r ^ 2 + s ^ 2)) x / Real.sqrt (r ^ 2 + s ^ 2) ^ n| ≤
      rho (Real.sqrt (r ^ 2 + s ^ 2)) x / Real.sqrt (r ^ 2 + s ^ 2) ^ n * (4 * ε) := by sorry

end RegevLWE.GaussConv
