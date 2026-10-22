-- Prove2me | Theorems.Thm_SpilloverDuopoly_Switchers_theorem_1
-- name    : SpilloverDuopoly.Switchers.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:40.563459+00:00
-- url     : https://prove2.me/theorems/3c0d535f-6cfe-47a5-ba5c-5c9db405c326
-- title:
--   Theorem 1, p. 20 (PDF 22) — in any symmetric equilibrium the first-period price is c − δ(π^{R∗} − π^{S∗}) and each firm earns δπ^{S∗}
-- statement:
--   Consider the two-period experience-goods duopoly with marginal cost $c\ge0$, discount factor $\delta\in[0,1]$ and tie share $\lambda\in[0,1]$. Let $\pi^{R*}$ and $\pi^{S*}$ be the second-period profits per unit of repeat and of switching consumers. Let $p$ be a symmetric first-period price at which consumers buy, $u_0\le V-p$. Then $(p,p)$ is an equilibrium of the first-period price game if and only if
--
--   $$
--   p=p^*=c-\delta\bigl(\pi^{R*}-\pi^{S*}\bigr),
--   $$
--
--   and in that equilibrium each firm's two-period profit is $\delta\pi^{S*}$.
--
--   This is the paper's Theorem 1: for every tie share $\lambda\in[0,1]$ and every form of the second-period equilibrium, firms make positive profit only through switching consumers. Profit is positive exactly when $\pi^{S*}>0$.
--
--   **Formalization Note** The paper states the theorem "for any $\rho\in[-1,1]$" and for any second-period equilibrium. $\rho$ enters only through $\pi^{R*},\pi^{S*}$, and these are arbitrary reals here, so all such cases are covered. The coverage hypothesis $u_0\le V-p$ is the paper's "$\lambda_i+\lambda_{-i}=1$" (p. 21), and it is necessary. With $c=1/2$, $\delta=1$, $\lambda=1/2$, $\pi^{R*}=1/5$, $\pi^{S*}=0$ and $V=u_0=0$, nobody buys at $p=1$, and $(1,1)$ is an equilibrium although $p^*=3/10$. The "if" direction is the paper's two deviation checks; the "only if" direction is "any symmetric equilibrium … is given by $p^*$".
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), p. 20 (PDF 22), Theorem 1; proof pp. 20–21 (PDF 22–23)

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Model

namespace SpilloverDuopoly.Switchers

/-- Theorem 1 (p. 20): for a symmetric price `p` at which consumers buy in the first period,
`(p, p)` is an equilibrium iff `p = c - δ (π^{R∗} - π^{S∗})`, and then each firm earns `δ π^{S∗}`. -/
theorem theorem_1 (G : Params) (hS : G.Standing) (p : ℝ) (hcov : G.u0 ≤ G.CS p) :
    (G.IsSymEq p ↔ p = G.pStar) ∧
    (G.IsSymEq p → G.profitA p p = G.delta * G.piS ∧ G.profitB p p = G.delta * G.piS) := by sorry

end SpilloverDuopoly.Switchers
