-- Prove2me | Theorems.Thm_RegevLWE_GaussConv_claim_3_9
-- name    : RegevLWE.GaussConv.claim_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:23.066003+00:00
-- url     : https://prove2.me/theorems/2a31ebcf-346f-42d1-9c77-94f9dafd8b68
-- title:
--   Claim 3.9 — D_{L+u,r} plus ν_s noise is within statistical distance 4ε of ν_t, t = √(r² + s²)
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice, let $u \in \mathbb{R}^n$ be any vector, let $r, s > 0$, and let $t := \sqrt{r^2 + s^2}$. Assume that
--   $$\frac{rs}{t} = \frac{1}{\sqrt{1/r^2 + 1/s^2}} \ge \eta_\epsilon(L)$$
--   for some $0 < \epsilon < \tfrac12$. Let $Y$ be the continuous distribution on $\mathbb{R}^n$ obtained by sampling from the discrete Gaussian $D_{L+u,r}$ and adding an independent noise vector distributed according to $\nu_s$; its density is $Y(x) = \sum_{y \in L+u} D_{L+u,r}(y)\,\nu_s(x - y)$. Then the statistical distance between $Y$ and $\nu_t$ is at most $4\epsilon$:
--   $$\Delta(Y, \nu_t) = \int_{\mathbb{R}^n} \bigl| Y(x) - \nu_t(x)\bigr|\,dx \le 4\epsilon .$$
--
--   When both Gaussians are sufficiently wide compared to the smoothing parameter, adding continuous Gaussian noise of width $s$ to a discrete Gaussian of width $r$ on a lattice coset produces, up to statistical distance $4\epsilon$, the continuous Gaussian of width $\sqrt{r^2+s^2}$ that one obtains for two continuous Gaussians. This is the input of Corollary 3.10 and of the classical step (Lemma 3.11) of Regev's reduction.
--
--   **Formalization Note** $\Delta$ is $\int|\varphi_1 - \varphi_2|$ with no factor $\tfrac12$ (p. 34:14), computed as a lower Lebesgue integral in $[0,\infty]$, so the bound cannot hold vacuously through a non-integrable difference. The hypothesis $\epsilon > 0$ is added (Definition 2.10 defines $\eta_\epsilon$ for $\epsilon > 0$ only; for $\epsilon \le 0$ the infimum would be over the empty set, equal to $0$ in Lean, and the hypothesis would be vacuous). $Y$ is given by its density, the formula the proof writes on its first line. No restriction on $n$: for $n = 0$ both densities equal $1$ at the single point of $\mathbb{R}^0$.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:25, Claim 3.9

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice

namespace RegevLWE.GaussConv

theorem claim_3_9 {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    [IsZLattice ℝ L] (u : EuclideanSpace ℝ (Fin n)) {r s ε : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (h : smoothingParam L ε ≤ r * s / Real.sqrt (r ^ 2 + s ^ 2)) :
    statDist (Ydensity L u r s) (nu (Real.sqrt (r ^ 2 + s ^ 2))) ≤ ENNReal.ofReal (4 * ε) := by sorry

end RegevLWE.GaussConv
