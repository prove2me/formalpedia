-- Prove2me | Theorems.Thm_RandomPromo_TwoPoint_proposition_3
-- name    : RandomPromo.TwoPoint.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:38.211983+00:00
-- url     : https://prove2.me/theorems/5e936483-bf85-49ad-b9cc-a91ca767b051
-- title:
--   Proposition 3, p. 16 — when Δ_R < 1 the two-point price distribution (β* at p*, 1 − β* at vH) is optimal for problem (2)
-- statement:
--   Under the standing assumptions $0<c_L<v_L<v_H$, $0<c_H<v_H$, $0<\alpha<1$, assume also $c_L<c_H$ and
--   $$\Delta_R=\sqrt{\frac{\alpha c_L}{(1-\alpha)(v_H-v_L)}}<1.$$
--   Let $U=U_1=\alpha v_L+(1-\alpha)v_H-(1-\alpha)c_L-2(1-\alpha)(v_H-v_L)\Delta_R$ if $\Delta_R<\frac{c_H-c_L}{v_H-v_L}$, and $U=U_2=\alpha v_L+(1-\alpha)v_H-(1-\alpha)c_H-\alpha c_L\frac{v_H-v_L}{c_H-c_L}$ otherwise. Then:
--   1. every finitely supported price distribution on $\mathbb R$ feasible for problem (2) earns at most $U$ in problem (2);
--   2. there is a function $\eta$ with $\lim_{\delta\searrow 0}\eta(\delta)=0$ such that, for all sufficiently small $\delta>0$, the two-point law
--   $$f(p)=\begin{cases}\beta^* & p=\underline p^*,\\ 1-\beta^* & p=v_H,\end{cases}\qquad \beta^*=\min\Big\{\Delta_R,\frac{c_H-c_L}{v_H-v_L}-\delta\Big\},\quad \underline p^*=v_L-\frac{c_L}{\beta^*}-\eta(\delta),$$
--   is a price distribution feasible for (2), and its profit in (2) tends to $U$ as $\delta\searrow 0$.
--
--   Together, the optimal value of problem (2) is $U$ and the two-point family attains it in the limit, which is the $\epsilon$-optimality of Definition 1.
--
--   **Formalization Note** "Optimal" is $\epsilon$-optimality (Definition 1) for problem (2), stated as an upper bound plus an approaching feasible family; this avoids dividing by the optimal value, which can be negative in case $U_2$. The function $\eta$ is existential, as in the paper, which only asserts $\eta(\delta)\to 0$. The hypothesis $c_L<c_H$ is added: without it $\beta^*<0$ and the two-point "distribution" is not one. Prices range over all of $\mathbb R$: $\underline p^*$ can be negative under the hypotheses, and with prices restricted to $[0,\infty)$ the proposition fails for some admissible parameters (e.g. $v_L=1$, $v_H=100$, $\alpha=1/2$, $c_L=1/2$, $c_H=50$, where no nonnegative law is feasible). The profit of the two-point law is computed from the general definitions of $\underline p^L$, $F$ and $\mathbb E[P\mid P\le x]$, not from a closed form.
-- source:
--   Chen, Hu, Wu, Intertemporal Price Discrimination via Randomized Promotions, SSRN preprint 3223844 (revision of 2022-11-16), p. 16, Proposition 3 and Definition 1; Online Supplement pp. 9–10, proof of Proposition 3

import Mathlib
import Definitions.Def_RandomPromo_TwoPoint_Setting

namespace RandomPromo.TwoPoint
theorem proposition_3 (M : Params) (hM : M.Standing) (hc : M.cL < M.cH) (hΔ : M.ΔR < 1) :
    (∀ w : ℝ →₀ ℝ, IsPriceDist w → M.Feas w →
        M.obj2 w ≤ (if M.ΔR < M.bnd then M.U1 else M.U2)) ∧
    ∃ η : ℝ → ℝ, Filter.Tendsto η (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      (∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
        IsPriceDist (M.twoPoint δ (η δ)) ∧ M.Feas (M.twoPoint δ (η δ))) ∧
      Filter.Tendsto (fun δ => M.obj2 (M.twoPoint δ (η δ))) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (if M.ΔR < M.bnd then M.U1 else M.U2)) := by sorry
end RandomPromo.TwoPoint
