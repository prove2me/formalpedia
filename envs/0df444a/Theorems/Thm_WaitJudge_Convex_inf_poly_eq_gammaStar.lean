-- Prove2me | Theorems.Thm_WaitJudge_Convex_inf_poly_eq_gammaStar
-- name    : WaitJudge.Convex.inf_poly_eq_gammaStar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:07:03.631558+00:00
-- url     : https://prove2.me/theorems/f5c9022c-0aa8-4346-8e86-d040af99fefb
-- title:
--   (24), Sect. 5.1.4, p. 18 — inf over feasible polynomials of p(1) equals γ*
-- statement:
--   Let $N,d$ be natural numbers and $\epsilon(0),\dots,\epsilon(d)\in[0,1]$. Let $\gamma^*$ be the value of the variational problem (10): the infimum of $\xi(1)$ over the functions $\xi\in C^d[0,1]$ with
--   $$\frac1{k!}\frac{\mathrm d^k}{\mathrm dt^k}\xi(t)\ \ge\ \binom Nk t^{N-k}\,\mathbf 1_{[0,1-\epsilon(k))}(t),\qquad t\in[0,1],\ k=0,1,\dots,d.$$
--   Then the infimum of $p(1)$ over the *polynomials* $p$ satisfying the same constraints equals $\gamma^*$:
--   $$\inf_{M}\gamma^*_M=\inf\{p(1):\ p\ \text{a real polynomial feasible for (10)}\}=\gamma^*.$$
--
--   Here $\gamma^*_M$ is the value of the dual problem (21) rewritten over polynomials of degree $M$, and the union over $M\ge d$ of these classes is the set of all real polynomials. The equality identifies the bound obtained by duality with the value of (10).
--
--   **Formalization Note** $C^d[0,1]$ is `ContDiffOn ℝ d` on $[0,1]$ with derivatives taken within $[0,1]$; a polynomial is feasible when its evaluation map is. Both infima are real `sInf`s of nonempty sets bounded below by $0$.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF pp. 17–18, Sect. 5.1.4, rewriting of (21) over P_M and (24)

import Mathlib
import Definitions.Def_WaitJudge_Convex_Setting

namespace WaitJudge.Convex

theorem inf_poly_eq_gammaStar (N d : ℕ) (ε : ℕ → ℝ) (hε : ∀ k ≤ d, 0 ≤ ε k ∧ ε k ≤ 1) :
    sInf {y | ∃ q : Polynomial ℝ, IsFeasible10 N d ε (fun t => q.eval t) ∧ y = q.eval 1} =
      gammaStar N d ε := by sorry

end WaitJudge.Convex
