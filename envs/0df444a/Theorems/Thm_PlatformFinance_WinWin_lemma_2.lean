-- Prove2me | Theorems.Thm_PlatformFinance_WinWin_lemma_2
-- name    : PlatformFinance.WinWin.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:26.448876+00:00
-- url     : https://prove2.me/theorems/79da9a2f-9907-438e-b5a3-5d8aced233ad
-- title:
--   Lemma 2, p. 13 — under platform financing the seller's unique best response to w is the Lemma 1 response to w(1+r)
-- statement:
--   Under platform financing at interest rate $r>-1$, the seller borrows $wq$ from the platform to pay the upfront wholesale price $w$ and owes $w(1+r)$ per unit at the end, with limited liability; her expected profit is $\Pi_s(w(1+r),q)=\mathbb E[((1-\varphi)(\tilde a-q)q-w(1+r)q)^+]$, with $\tilde a\sim U[a-\delta,a+\delta]$, $\delta>0$, $0\le\varphi<1$.
--
--   If $w(1+r)<(1-\varphi)(a+\delta)$, then
--   $$q(w)=\begin{cases}\dfrac{(1-\varphi)a-w(1+r)}{2(1-\varphi)}&\text{if } w\le\dfrac{(1-\varphi)(a-2\delta)}{1+r},\\[2mm]\dfrac{(1-\varphi)(a+\delta)-w(1+r)}{3(1-\varphi)}&\text{if } w>\dfrac{(1-\varphi)(a-2\delta)}{1+r}\end{cases}$$
--   is nonnegative and is the unique maximizer of the seller's expected profit over $q\ge0$.
--
--   **Formalization Note.** Stated as Lemma 1's best response evaluated at $W=w(1+r)$; the threshold $w(1+r)\le(1-\varphi)(a-2\delta)$ is the page's $w\le(1-\varphi)(a-2\delta)/(1+r)$ because $1+r>0$. The hypothesis $w(1+r)<(1-\varphi)(a+\delta)$ excludes prices at which every order earns $0$ (proof of Proposition 2, p. 33).
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 13, Lemma 2; proof p. 33

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

namespace PlatformFinance.WinWin
theorem lemma_2 (a δ φ r w : ℝ) (hδ : 0 < δ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hr : -1 < r)
    (hw : w * (1 + r) < (1 - φ) * (a + δ)) :
    0 ≤ qBR a δ φ (w * (1 + r)) ∧
      ∀ q : ℝ, 0 ≤ q → q ≠ qBR a δ φ (w * (1 + r)) →
        sellerPayoff a δ φ (w * (1 + r)) q <
          sellerPayoff a δ φ (w * (1 + r)) (qBR a δ φ (w * (1 + r))) := by sorry
end PlatformFinance.WinWin
