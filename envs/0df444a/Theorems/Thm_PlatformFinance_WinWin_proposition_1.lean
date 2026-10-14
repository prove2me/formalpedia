-- Prove2me | Theorems.Thm_PlatformFinance_WinWin_proposition_1
-- name    : PlatformFinance.WinWin.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:22.345662+00:00
-- url     : https://prove2.me/theorems/a0a44507-c32d-4190-b25d-af1eedbac69d
-- title:
--   Proposition 1, p. 11 — the trade-credit game has an equilibrium, and every equilibrium has price w^T and order q^T (switching at δ₁)
-- statement:
--   Consider the trade-credit game: the supplier (unit cost $c>0$, capital cost $r_f\ge0$) sets a deferred wholesale price $w$, then the seller orders $q\ge0$, sells at $\tilde a-q$ with $\tilde a\sim U[a-\delta,a+\delta]$, keeps $(1-\varphi)$ of revenue and repays $\min\{(1-\varphi)(\tilde a-q)q,\,wq\}$. Assume $0<\delta<a$, $0\le\varphi<1$ and $(1-\varphi)a>c(1+r_f)$. Let
--   $$\delta_1=\frac{(5\sqrt{10}-14)\big((1-\varphi)a-c(1+r_f)\big)}{8(1-\varphi)},\qquad S=\sqrt{\frac{(\delta+3a)(1-\varphi)-3c(1+r_f)}{\delta(1-\varphi)}}.$$
--   Then a subgame-perfect equilibrium exists, and in every subgame-perfect equilibrium the wholesale price and the order quantity on the equilibrium path are
--   $$w^T=\begin{cases}\dfrac{(1-\varphi)a+c(1+r_f)}{2}&\delta\le\delta_1,\\[2mm](1-\varphi)\big(a-\delta(S-2)\big)&\delta>\delta_1,\end{cases}\qquad q^T=\begin{cases}\dfrac{(1-\varphi)a-c(1+r_f)}{4(1-\varphi)}&\delta\le\delta_1,\\[2mm]\dfrac{\delta}{3}(S-1)&\delta>\delta_1.\end{cases}$$
--
--   For small uncertainty the supplier prices so that the seller never defaults; above $\delta_1$ he raises the price and accepts default risk.
--
--   **Formalization Note.** Equilibrium includes the seller's tie-break (she orders $0$ when no order is profitable) and the supplier's least-price tie-break, which is the paper's assignment of $\delta=\delta_1$ to the first branch (p. 32). The $\delta>\delta_1$ branch is the proof's form (p. 31, $w_2$; (3), p. 36): the statement on p. 11 prints $\sqrt{(\delta+3a)-3c(1+r_f)/(1-\varphi)}$, which lacks a factor $\delta$ under the root. The hypothesis $\delta<a$ formalizes the standing assumption that the smallest market size $a-\delta$ keeps the price positive (p. 8).
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 11, Proposition 1; proof pp. 30–33 (w₂ p. 31)

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

namespace PlatformFinance.WinWin
theorem proposition_1 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a) :
    (∃ σ : Profile, IsSPET a δ φ c rf σ) ∧
      ∀ σ : Profile, IsSPET a δ φ c rf σ →
        σ.w = wT a δ φ c rf ∧ σ.order σ.w = qT a δ φ c rf := by sorry
end PlatformFinance.WinWin
