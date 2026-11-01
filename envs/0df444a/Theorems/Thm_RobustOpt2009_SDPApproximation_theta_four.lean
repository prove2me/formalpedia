-- Prove2me | Theorems.Thm_RobustOpt2009_SDPApproximation_theta_four
-- name    : RobustOpt2009.SDPApproximation.theta_four
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T06:48:38.697115+00:00
-- url     : https://prove2.me/theorems/d4dd34a2-7ed9-4595-87a1-51c7f9e6dd0e
-- title:
--   $\vartheta(4)=2$ — the rank-four value of the real Matrix Cube tightness function
-- statement:
--   Let $\xi=(\xi_1,\ldots,\xi_k)$ be a standard Gaussian vector in $\mathbb R^k$ and let
--   $$\vartheta(k)^{-1}=\min\Bigl\{\,\mathbb E\Bigl|\sum_{\ell=1}^k\alpha_\ell\,\xi_\ell^2\Bigr| \;:\; \alpha\in\mathbb R^k,\ \|\alpha\|_1=1\Bigr\}$$
--   be the universal function of the real Matrix Cube Theorem (the function $\theta$ of (4.4.38) in Ben-Tal–Nemirovski's *Lectures on Modern Convex Optimization*, i.e. $\vartheta_S$ of (B.4.25) in *Robust Optimization*; on the platform it is `ModernConvex.MatrixCube.theta`, written with the Gaussian density on $\mathbb R^k$).
--
--   **Claim.**
--   $$\vartheta(4)=2,\qquad\text{i.e.}\qquad \min_{\|\alpha\|_1=1}\ \mathbb E\Bigl|\sum_{\ell=1}^4\alpha_\ell\xi_\ell^2\Bigr|=\frac12 .$$
--
--   This is the value $\vartheta(4)=2$ asserted in Theorem 7.1.3 (ii) and Theorem B.4.14 (iii) of Ben-Tal, El Ghaoui and Nemirovski. Together with the already-proved bounds $\vartheta(2)=\pi/2$, $\vartheta(k)\le\pi\sqrt k/2$ and Lemma 4.4.4 ($\mathbb E|\xi^TA\xi|\ge\|\lambda(A)\|_1/\vartheta(\operatorname{rank}A)$), it is the remaining ingredient of the rank-sensitive tightness bound of the real mixed-block Matrix Cube Theorem: for perturbation matrices of rank at most four the semidefinite certificate is tight within the factor $2$.
--
--   The value $1/2$ is attained at $\alpha=(\tfrac14,\tfrac14,-\tfrac14,-\tfrac14)$, where $\tfrac14(\xi_1^2+\xi_2^2-\xi_3^2-\xi_4^2)$ is a quarter of a difference of two independent $\chi^2_2$ (exponential, mean $2$) variables, a Laplace variable with $\mathbb E|\cdot|=2$. The substantive direction is the lower bound $\mathbb E|\sum_\ell\alpha_\ell\xi_\ell^2|\ge\tfrac12$ for every $\alpha$ on the $\ell_1$ sphere of $\mathbb R^4$.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem 7.1.3 (ii) (printed p. 183, PDF p. 209: ϑ(4) = 2) and Theorem B.4.14 (iii) (printed p. 507); ϑ as in Proposition B.4.10, (B.4.25) (printed p. 500), equivalently θ of (4.4.38) in Ben-Tal–Nemirovski, Lectures on Modern Convex Optimization, p. 191

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

namespace RobustOpt2009.SDPApproximation

/-- The universal tightness function of the real Matrix Cube Theorem at rank four:
`ϑ(4) = 2`, for `ϑ = θ` the function of (4.4.38) / (B.4.25). -/
theorem theta_four : ModernConvex.MatrixCube.theta 4 = 2 := by sorry

end RobustOpt2009.SDPApproximation
