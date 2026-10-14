-- Prove2me | Theorems.Thm_PlatformFinance_PlatformProfit_lemma_1
-- name    : PlatformFinance.PlatformProfit.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:32.256056+00:00
-- url     : https://prove2.me/theorems/48b3658d-d5a2-4388-a0c2-9b193786ac2d
-- title:
--   Lemma 1, p. 10 — the seller's unique best response to an owed amount W is ((1−φ)a−W)/(2(1−φ)) or ((1−φ)(a+δ)−W)/(3(1−φ))
-- statement:
--   Let $\delta>0$, $0\le\varphi<1$, and let the market size $\tilde a$ be uniform on $[a-\delta,a+\delta]$. A seller who orders $q\ge 0$ units, sells them at the price $\tilde a-q$, keeps the share $1-\varphi$ of the revenue and owes $W$ per unit at the end, with limited liability, earns
--   $$
--   \Pi_s(q)=\mathbb E\big[((1-\varphi)(\tilde a-q)q-Wq)^+\big].
--   $$
--   If $W<(1-\varphi)(a+\delta)$, then $\Pi_s$ has a unique maximizer over $q\ge 0$, namely
--   $$
--   q(W)=\begin{cases}\dfrac{(1-\varphi)a-W}{2(1-\varphi)} & \text{if } W\le(1-\varphi)(a-2\delta),\\[2mm] \dfrac{(1-\varphi)(a+\delta)-W}{3(1-\varphi)} & \text{if } W>(1-\varphi)(a-2\delta),\end{cases}
--   $$
--   and $q(W)\ge 0$. Under trade credit $W$ is the deferred wholesale price $w$.
--
--   The first branch is the order at which the seller never defaults; in the second she targets the high market realizations and defaults on the low ones. This best response is the seller's stage of the trade-credit game and, with $W=w(1+r)$, of the platform-financing game.
--
--   **Formalization Note** The page states the result for every $w$; for $W\ge(1-\varphi)(a+\delta)$ every order earns zero and the printed second branch is negative, so the hypothesis $W<(1-\varphi)(a+\delta)$ is added (the proof of Proposition 1, p. 31, restricts to such prices for this reason). The lemma is stated for a generic owed amount $W$, as the paper does on p. 33. Uniqueness is stated explicitly.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 10, Lemma 1; proof pp. 30–31

import Mathlib
import Definitions.Def_PlatformFinance_PlatformProfit_Model

namespace PlatformFinance.PlatformProfit

/-- Lemma 1 (p. 10): when the seller owes `W < (1 − φ)(a + δ)` per unit at the end, her expected
profit `E[((1 − φ)(ã − q)q − Wq)⁺]` has the unique maximizer `qBR a δ φ W` over `q ≥ 0`. -/
theorem lemma_1 (a δ φ W : ℝ) (hδ : 0 < δ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hW : W < (1 - φ) * (a + δ)) :
    0 ≤ qBR a δ φ W ∧
      ∀ q : ℝ, 0 ≤ q → q ≠ qBR a δ φ W →
        PlatformFinance.WinWin.sellerPayoff a δ φ W q < PlatformFinance.WinWin.sellerPayoff a δ φ W (qBR a δ φ W) := by sorry

end PlatformFinance.PlatformProfit
