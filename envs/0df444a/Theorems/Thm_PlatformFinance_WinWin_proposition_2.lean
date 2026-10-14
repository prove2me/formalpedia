-- Prove2me | Theorems.Thm_PlatformFinance_WinWin_proposition_2
-- name    : PlatformFinance.WinWin.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:33.052011+00:00
-- url     : https://prove2.me/theorems/d4cded4f-4eaa-4f5e-931e-04979037fdcb
-- title:
--   Proposition 2, p. 13 — the platform-financing game has an equilibrium, and every equilibrium has price w^P and order q^P (switching at δ_r)
-- statement:
--   Consider the platform-financing game at loan rate $r$: the supplier sets an upfront wholesale price $w$ and earns $(w-c)q(1+r_f)$; the seller orders $q\ge0$, borrows $wq$ from the platform and owes $w(1+r)q$, with limited liability. Assume the standing conditions $0<\delta<a$, $0\le\varphi<1$, $c>0$, $r_f\ge0$, $(1-\varphi)a>c(1+r_f)$, together with $r>-1$ and $c(1+r)<(a+\delta)(1-\varphi)$. Let
--   $$\delta_r=\frac{a(1-\varphi)-c(1+r)}{(2+\sqrt6)(1-\varphi)}.$$
--   Then a subgame-perfect equilibrium exists, and in every subgame-perfect equilibrium
--   $$w^P=\begin{cases}\dfrac{(1-\varphi)a+c(1+r)}{2(1+r)}&\delta\le\delta_r,\\[2mm]\dfrac{(1-\varphi)(a+\delta)+c(1+r)}{2(1+r)}&\delta>\delta_r,\end{cases}\qquad q^P=\begin{cases}\dfrac{(1-\varphi)a-c(1+r)}{4(1-\varphi)}&\delta\le\delta_r,\\[2mm]\dfrac{(1-\varphi)(a+\delta)-c(1+r)}{6(1-\varphi)}&\delta>\delta_r.\end{cases}$$
--
--   **Formalization Note.** Equilibrium includes the seller's tie-break and the supplier's least-price tie-break (the paper's assignment of $\delta=\delta_r$ to the first branch). The conditions $r>-1$ and $c(1+r)<(a+\delta)(1-\varphi)$ are the paper's conditions (iii) and (ii), p. 36.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 13, Proposition 2; proof pp. 33–35; conditions (ii)–(iii) p. 36

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

namespace PlatformFinance.WinWin
theorem proposition_2 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ)) :
    (∃ σ : Profile, IsSPEP a δ φ c rf r σ) ∧
      ∀ σ : Profile, IsSPEP a δ φ c rf r σ →
        σ.w = wP a δ φ c r ∧ σ.order σ.w = qP a δ φ c r := by sorry
end PlatformFinance.WinWin
