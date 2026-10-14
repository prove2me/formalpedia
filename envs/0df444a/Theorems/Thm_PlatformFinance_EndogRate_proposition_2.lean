-- Prove2me | Theorems.Thm_PlatformFinance_EndogRate_proposition_2
-- name    : PlatformFinance.EndogRate.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:36.230988+00:00
-- url     : https://prove2.me/theorems/cc193a93-eccb-4bcd-b148-780590e5b8f8
-- title:
--   Proposition 2, p. 13 — existence and closed form of the platform-financing equilibrium
-- statement:
--   Consider the platform-financing game at loan rate $r$: the supplier sets the upfront wholesale price $w$, then the seller, owing $w(1+r)$ per unit, chooses her order. Assume $0<\delta<a$, $0\le\varphi<1$, $c>0$, $r_f\ge 0$, $(1-\varphi)a > c(1+r_f)$, $r>-1$ and $c(1+r) < (a+\delta)(1-\varphi)$. Let $\delta_r = \frac{a(1-\varphi)-c(1+r)}{(2+\sqrt6)(1-\varphi)}$. Then a subgame-perfect equilibrium exists, and in every subgame-perfect equilibrium the wholesale price and the order on the equilibrium path are
--
--   $$w^P=\begin{cases}\dfrac{(1-\varphi)a+c(1+r)}{2(1+r)} & \delta\le\delta_r,\\[2ex] \dfrac{(1-\varphi)(a+\delta)+c(1+r)}{2(1+r)} & \delta>\delta_r,\end{cases}\qquad q^P=\begin{cases}\dfrac{(1-\varphi)a-c(1+r)}{4(1-\varphi)} & \delta\le\delta_r,\\[2ex] \dfrac{(1-\varphi)(a+\delta)-c(1+r)}{6(1-\varphi)} & \delta>\delta_r.\end{cases}$$
--
--   This is the equilibrium on which every statement about the platform's profit rests; in particular it shows the family of equilibria assumed in Proposition 8 exists.
--
--   **Formalization Note** The equilibrium includes the two tie-breaks of the model file: the seller orders zero when no order is profitable, and the supplier's price is the least optimal one, which assigns $\delta=\delta_r$ to the first branch, as the page does. The hypotheses $r>-1$ and $c(1+r)<(a+\delta)(1-\varphi)$ are conditions (iii) and (ii) of p. 36; $\delta<a$ is the reading of "the smallest market size $a-\delta$ is large enough so that the market clearing price is always positive" (p. 8).
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 13, Proposition 2; proof pp. 33–35; conditions (ii)–(iii), p. 36

import Mathlib
import Definitions.Def_PlatformFinance_EndogRate_Model

namespace PlatformFinance.EndogRate

/-- Proposition 2 (p. 13): the platform-financing game at rate `r` has a subgame-perfect
equilibrium, and in every one the wholesale price is `w^P` and the order on the path is `q^P`. -/
theorem proposition_2 (a δ φ c rf r : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ)) :
    (∃ σ : Profile, IsSPEP a δ φ c rf r σ) ∧
      ∀ σ : Profile, IsSPEP a δ φ c rf r σ →
        σ.w = wP a δ φ c r ∧ σ.order σ.w = qP a δ φ c r := by sorry

end PlatformFinance.EndogRate
