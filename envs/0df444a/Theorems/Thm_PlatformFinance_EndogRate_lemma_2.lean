-- Prove2me | Theorems.Thm_PlatformFinance_EndogRate_lemma_2
-- name    : PlatformFinance.EndogRate.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:38.148585+00:00
-- url     : https://prove2.me/theorems/150ae6f5-085e-49f4-8b15-432356b12573
-- title:
--   Lemma 2, p. 13 — the seller's unique best response under platform financing
-- statement:
--   Under platform financing with loan rate $r>-1$ and upfront wholesale price $w$, the seller owes $W = w(1+r)$ per unit and chooses $q\ge 0$ to maximize $\Pi_s(W,q)=\mathbb E[((1-\varphi)(\tilde a-q)q - Wq)^+]$, with $\tilde a\sim U[a-\delta,a+\delta]$, $\delta>0$, $0\le\varphi<1$. If $w(1+r) < (1-\varphi)(a+\delta)$, her unique optimal order is
--
--   $$q(w)=\begin{cases}\dfrac{(1-\varphi)a-w(1+r)}{2(1-\varphi)} & \text{if } w \le \dfrac{(1-\varphi)(a-2\delta)}{1+r},\\[2ex] \dfrac{(1-\varphi)(a+\delta)-w(1+r)}{3(1-\varphi)} & \text{if } w > \dfrac{(1-\varphi)(a-2\delta)}{1+r},\end{cases}$$
--
--   which is nonnegative, and every other $q\ge 0$ gives strictly lower expected profit.
--
--   The first branch is the order that never defaults; the second allows default in low markets. This best response is the seller's stage of the platform-financing game.
--
--   **Formalization Note** The hypothesis $w(1+r) < (1-\varphi)(a+\delta)$ is pinned: the proof of Proposition 2 (p. 33) restricts to this range "because otherwise the seller's optimal order quantity is zero" (every order then yields zero profit and the maximizer is not unique). The branch condition is stated with $W=w(1+r)$, equivalent since $1+r>0$.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 13, Lemma 2; proof pp. 33–34

import Mathlib
import Definitions.Def_PlatformFinance_EndogRate_Model

namespace PlatformFinance.EndogRate

/-- Lemma 2 (p. 13): under platform financing, given the loan rate `r` and the upfront price
`w` with `w(1 + r) < (1 - φ)(a + δ)`, the seller's best response `qBR a δ φ (w(1 + r))` is the
unique maximizer of her expected profit over `q ≥ 0`. -/
theorem lemma_2 (a δ φ r w : ℝ) (hδ : 0 < δ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hr : -1 < r)
    (hw : w * (1 + r) < (1 - φ) * (a + δ)) :
    0 ≤ qBR a δ φ (w * (1 + r)) ∧
      ∀ q : ℝ, 0 ≤ q → q ≠ qBR a δ φ (w * (1 + r)) →
        sellerPayoff a δ φ (w * (1 + r)) q < sellerPayoff a δ φ (w * (1 + r)) (qBR a δ φ (w * (1 + r))) := by sorry

end PlatformFinance.EndogRate
