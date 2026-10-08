-- Prove2me | Theorems.Thm_WaitJudge_Convex_iteratedDeriv_pow_div_factorial
-- name    : WaitJudge.Convex.iteratedDeriv_pow_div_factorial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:45:14.507913+00:00
-- url     : https://prove2.me/theorems/878ff154-fbcb-4998-b4f8-1a1ae71a38e3
-- title:
--   (23), Sect. 5.1.4, p. 17 — (1/k!) dᵏ/dtᵏ tᵐ = 0 for m < k and C(m,k) t^(m−k) for m ≥ k
-- statement:
--   For all natural numbers $k,m$ and every real $t$,
--   $$\frac1{k!}\frac{\mathrm d^k}{\mathrm dt^k}t^m=\begin{cases}0,& m<k,\\[2pt] \binom mk t^{m-k},& m\ge k.\end{cases}$$
--
--   In the proof of Theorem 1 this identity turns the constraints of the dual problem (21), after the substitution $t=1-v$, into derivative constraints on the polynomial $p(t)=\sum_{m=0}^M\lambda_m t^m$, which is how the variational problem (10) arises.
--
--   **Formalization Note** The $k$-th derivative is Mathlib's `iteratedDeriv k`, and $k=0$ means no derivative is taken.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF p. 17, Sect. 5.1.4, (23)

import Mathlib

namespace WaitJudge.Convex

theorem iteratedDeriv_pow_div_factorial (k m : ℕ) (t : ℝ) :
    (1 / (k.factorial : ℝ)) * iteratedDeriv k (fun t : ℝ => t ^ m) t =
      if m < k then 0 else (m.choose k : ℝ) * t ^ (m - k) := by sorry

end WaitJudge.Convex
