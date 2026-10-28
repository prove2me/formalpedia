-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_lower_decomposition
-- name    : ScheduledQueue.Stability.lower_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:07.539108+00:00
-- url     : https://prove2.me/theorems/588fc746-1297-40ff-9c8a-706fc43fedfc
-- title:
--   Proof of Theorem 1, pp. 6–7 — lower decomposition n + Ỹ_n ≤ Λ(nh)/h + Y_n + Γ₂
-- statement:
--   Fix one outcome of the scheduled-traffic model with $h>0$ and $U\in[0,1]$, and let $R_j=jh+Uh-\xi_j$. For every $n=0,1,2,\dots$,
--   $$n+\tilde Y_n\;\le\;\#\{j\in\mathbb Z: R_j\in(0,nh]\}+Y_n+\Gamma_2,$$
--   where $\tilde Y_n=\sum_{j\ge1}I(\xi^+_{n+j}\ge(j+2)h)$, $Y_n=\sum_{j\ge1}I(-\xi_{n+1-j}>(j-2)h)$ and $\Gamma_2=\sum_{j\ge1}I(\xi_j\ge(j-1)h)$. Equivalently, whenever all these counts are finite,
--   $$\Lambda(nh)-nh\;\ge\;h\big(\tilde Y_n-Y_n-\Gamma_2\big).$$
--
--   This is the lower bound of the proof of Theorem 1: along times $n$ at which $Y_n$ is small and $\tilde Y_n$ is large, $\Lambda(nh)-nh$ is large, which is how unbounded perturbations make $M(\infty)$ infinite.
--
--   **Formalization Note.** The page derives the bound from "$\beta_4(s)\le Y_{k(s)}$", "$\beta_2(s)\ge\tilde Y_{k(s)}$" and $\beta_3\le\Gamma_2$. The second inequality is false as printed (a very large $\xi_{k+j}$ puts that customer's reversed arrival below $0$, so $\beta_2$ does not count it), and the printed $Y$ has the wrong sign; the statement here is the corrected inequality, in which such customers are counted once in $\Gamma_2$. All counts are valued in $\mathbb N\cup\{\infty\}$, where there is no subtraction, so the inequality is written additively.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, pp. 6–7, proof of Theorem 1, displays β₄(s) ≤ Y_{k(s)}, β₂(s) ≥ Ỹ_{k(s)}, β₃(s) ≤ Γ₂ and max_{s≥0} Λ(s) − s ≥ lim sup β₂(τᵢh) − Γ₂ − Y_{τᵢ} (corrected)

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem lower_decomposition {Ω : Type*} (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ)
    (U : Ω → ℝ) :
    ∀ ω, U ω ∈ Icc (0 : ℝ) 1 → ∀ n : ℕ,
      (n : ℕ∞) + tildeY h ξ n ω ≤ revCount h ξ U (n * h) ω + Y h ξ n ω + gamma2 h ξ ω := by sorry

end ScheduledQueue.Stability
