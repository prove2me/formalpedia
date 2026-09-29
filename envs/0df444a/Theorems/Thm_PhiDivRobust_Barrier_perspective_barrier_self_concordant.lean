-- Prove2me | Theorems.Thm_PhiDivRobust_Barrier_perspective_barrier_self_concordant
-- name    : PhiDivRobust.Barrier.perspective_barrier_self_concordant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:57:24.341991+00:00
-- url     : https://prove2.me/theorems/1ee97aff-9eb8-4c8f-9489-4c28da6e0c14
-- title:
--   Theorem 2 — the barrier −ln(z − y f(s/y)) − ln s − ln y is (2 + (√2/3)κ)-self-concordant
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be convex and three times continuously differentiable on $(0,\infty)$, and suppose that for some $\kappa>0$
--
--   $$|f'''(s)|\le\kappa\,\frac{f''(s)}{s}\qquad\text{for all } s>0.\tag{33}$$
--
--   Then the logarithmic barrier function for $\{yf(s/y)\le z,\ s\ge0,\ y\ge0\}$ (34), given by
--
--   $$\varphi_B(s,y,z)=-\ln\bigl(z-yf(s/y)\bigr)-\ln s-\ln y,\tag{35}$$
--
--   is $\bigl(2+(\sqrt2/3)\kappa\bigr)$-self-concordant (Definition 1) on its domain $F_f=\{(s,y,z):s>0,\ y>0,\ yf(s/y)<z\}$: $F_f$ is open and convex, $\varphi_B$ is $C^3$ on $F_f$, and for every $(s,y,z)\in F_f$ and every $h\in\mathbb R^3$
--
--   $$\bigl|\nabla^3\varphi_B(s,y,z)[h,h,h]\bigr|\le 2\Bigl(2+\tfrac{\sqrt2}{3}\kappa\Bigr)\bigl(h^{\mathsf T}\nabla^2\varphi_B(s,y,z)h\bigr)^{3/2}.$$
--
--   Applied with $f(s)=\phi^*(u-s)$ (Burg entropy) or $f(s)=(\tilde\phi)^*(\tilde u-s)$ (Kullback–Leibler), the theorem makes the robust counterparts of linear constraints under these φ-divergence uncertainty sets tractable by interior-point methods.
--
--   **Formalization Note** "$f:\mathbb R^+\to\mathbb R$" is read as $f$ defined, convex and $C^3$ on $(0,\infty)$; the $C^3$ regularity is implicit on the page (condition (33) uses $f'''$ and Definition 1 requires $\varphi_B\in C^3$). $f''$ and $f'''$ are `iteratedDeriv 2 f` and `iteratedDeriv 3 f`. The constant is stated as printed, $2+\sqrt2/3\cdot\kappa$, for the same $\kappa$ as in (33).
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 350, Theorem 2, Eqs. (33)–(35)

import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_IsSelfConcordant
import Definitions.Def_PhiDivRobust_Barrier_perspective
import Definitions.Def_PhiDivRobust_Barrier_logBarrier

namespace PhiDivRobust.Barrier

theorem perspective_barrier_self_concordant (f : ℝ → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioi 0) f) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (hκ : 0 < κ)
    (h33 : ∀ s : ℝ, 0 < s → |iteratedDeriv 3 f s| ≤ κ * iteratedDeriv 2 f s / s) :
    IsSelfConcordant (2 + Real.sqrt 2 / 3 * κ) (barrierDomain f) (logBarrier f) := by sorry

end PhiDivRobust.Barrier
