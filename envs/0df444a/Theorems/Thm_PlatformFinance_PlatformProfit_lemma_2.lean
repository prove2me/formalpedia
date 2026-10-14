-- Prove2me | Theorems.Thm_PlatformFinance_PlatformProfit_lemma_2
-- name    : PlatformFinance.PlatformProfit.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:30.754457+00:00
-- url     : https://prove2.me/theorems/ffe53fba-1863-4f7a-8332-a4595c49fcb4
-- title:
--   Lemma 2, p. 13 — under platform financing the seller's unique best response is Lemma 1's with owed amount w(1+r)
-- statement:
--   Let $\delta>0$, $0\le\varphi<1$, $r>-1$, and let the market size $\tilde a$ be uniform on $[a-\delta,a+\delta]$. Under platform financing the seller borrows $wq$ at rate $r$ to pay the upfront wholesale price $w$, and earns
--   $$
--   \Pi_s(q)=\mathbb E\big[((1-\varphi)(\tilde a-q)q-wq(1+r))^+\big].
--   $$
--   If $w(1+r)<(1-\varphi)(a+\delta)$, then $\Pi_s$ has a unique maximizer over $q\ge0$, namely
--   $$
--   q(w)=\begin{cases}\dfrac{(1-\varphi)a-w(1+r)}{2(1-\varphi)} & \text{if } w\le\dfrac{(1-\varphi)(a-2\delta)}{1+r},\\[2mm] \dfrac{(1-\varphi)(a+\delta)-w(1+r)}{3(1-\varphi)} & \text{if } w>\dfrac{(1-\varphi)(a-2\delta)}{1+r},\end{cases}
--   $$
--   and $q(w)\ge0$.
--
--   It is the seller's stage of the platform-financing game: the repayment $w(1+r)$ plays the role of the deferred price of Lemma 1.
--
--   **Formalization Note** The best response is written as Lemma 1's function evaluated at $W=w(1+r)$; its branch test $w(1+r)\le(1-\varphi)(a-2\delta)$ is the page's $w\le(1-\varphi)(a-2\delta)/(1+r)$ because $1+r>0$. The hypothesis $w(1+r)<(1-\varphi)(a+\delta)$ is added for the same reason as in Lemma 1.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 13, Lemma 2; proof p. 33

import Mathlib
import Definitions.Def_PlatformFinance_PlatformProfit_Model

namespace PlatformFinance.PlatformProfit

/-- Lemma 2 (p. 13): under platform financing at rate `r > −1` and upfront price `w` with
`w(1 + r) < (1 − φ)(a + δ)`, the seller's expected profit `E[((1 − φ)(ã − q)q − wq(1 + r))⁺]` has
the unique maximizer `qBR a δ φ (w(1 + r))` over `q ≥ 0`. -/
theorem lemma_2 (a δ φ r w : ℝ) (hδ : 0 < δ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hr : -1 < r)
    (hw : w * (1 + r) < (1 - φ) * (a + δ)) :
    0 ≤ qBR a δ φ (w * (1 + r)) ∧
      ∀ q : ℝ, 0 ≤ q → q ≠ qBR a δ φ (w * (1 + r)) →
        PlatformFinance.WinWin.sellerPayoff a δ φ (w * (1 + r)) q <
          PlatformFinance.WinWin.sellerPayoff a δ φ (w * (1 + r)) (qBR a δ φ (w * (1 + r))) := by sorry

end PlatformFinance.PlatformProfit
