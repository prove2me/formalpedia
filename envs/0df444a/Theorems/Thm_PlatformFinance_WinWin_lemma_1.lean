-- Prove2me | Theorems.Thm_PlatformFinance_WinWin_lemma_1
-- name    : PlatformFinance.WinWin.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:20.204978+00:00
-- url     : https://prove2.me/theorems/36592e8a-3b6c-41cf-8218-3a9d0f46c60a
-- title:
--   Lemma 1, p. 10 — the seller's unique best response to the amount W she owes is ((1−φ)a − W)/(2(1−φ)) or ((1−φ)(a+δ) − W)/(3(1−φ))
-- statement:
--   Let the market size $\tilde a$ be uniform on $[a-\delta,a+\delta]$ with $\delta>0$, let the seller keep the share $1-\varphi$ of revenue with $0\le\varphi<1$, and suppose she owes $W$ per unit procured at the end of the season, with limited liability. Her expected profit from procuring $q\ge0$ units is $\Pi_s(W,q)=\mathbb E[((1-\varphi)(\tilde a-q)q-Wq)^+]$.
--
--   If $W<(1-\varphi)(a+\delta)$, then
--   $$q(W)=\begin{cases}\dfrac{(1-\varphi)a-W}{2(1-\varphi)} & \text{if } W\le(1-\varphi)(a-2\delta),\\[2mm] \dfrac{(1-\varphi)(a+\delta)-W}{3(1-\varphi)} & \text{if } W>(1-\varphi)(a-2\delta)\end{cases}$$
--   is nonnegative and is the unique maximizer of $q\mapsto\Pi_s(W,q)$ over $q\ge0$: every other $q\ge0$ earns strictly less.
--
--   Under trade credit $W$ is the deferred wholesale price $w$; this is Lemma 1 of the paper. The first branch is the no-default order, the second the order of a risk-seeking seller who accepts default at low market sizes.
--
--   **Formalization Note.** The lemma is stated for a generic owed amount $W$ so that Lemma 2 is its instance $W=w(1+r)$. The hypothesis $W<(1-\varphi)(a+\delta)$ is added: for larger $W$ every order earns $0$ and the maximizer is not unique; the proof of Proposition 1 (p. 31) restricts to this range for the same reason.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 10, Lemma 1 (payoff (1), p. 10); proof p. 30

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

namespace PlatformFinance.WinWin
theorem lemma_1 (a δ φ W : ℝ) (hδ : 0 < δ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hW : W < (1 - φ) * (a + δ)) :
    0 ≤ qBR a δ φ W ∧
      ∀ q : ℝ, 0 ≤ q → q ≠ qBR a δ φ W →
        sellerPayoff a δ φ W q < sellerPayoff a δ φ W (qBR a δ φ W) := by sorry
end PlatformFinance.WinWin
