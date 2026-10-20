-- Prove2me | Theorems.Thm_ReserveLP_ProLPR_lemma_5_3
-- name    : ReserveLP.ProLPR.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:26.394058+00:00
-- url     : https://prove2.me/theorems/fb8c9a47-c86a-43de-b002-962e440cbf79
-- title:
--   Lemma 5.3, p. 11 — the second condition holds with c = max over θ ∈ [0,1] of OPT(θ)
-- statement:
--   Let $(s^\star,q^\star)$ be an optimal solution of Profile-LP, and let $r^{\mathcal R}$ be the random reserve vector of the Pro-LPR rounding. Let $n=|\mathsf B|$ be the number of buyers, auxiliary buyers included, and let
--
--   $$c=\max_{\theta\in[0,1]}\mathsf{OPT}(\theta),$$
--
--   where $\mathsf{OPT}(\theta)$ is the optimal value of Problem (10) with $n$ variables. Then for every auction $a$ and every $t\le\beta^{(2)}_a$,
--
--   $$\sum_{p\in\mathcal P_a,\ \mathrm{Rev}_a(p)\ge t}s^\star_{a,p}-\Pr\big[\mathrm{Rev}_a(r^{\mathcal R})\ge t\big]\ \le\ c.$$
--
--   This is condition (3) of Lemma 5.1. It reduces the approximation factor to the value of the nonlinear program (10).
--
--   **Formalization Note.** $c$ is the supremum of $\mathsf{OPT}$ over $[0,1]$, and $\mathsf{OPT}$ is a supremum over the feasible set of (10). Both are well defined because $n\ge2$ (the two auxiliary buyers are distinct). For $t<0$ the claim is immediate, so no lower bound on $t$ is imposed; the page imposes none either.
-- source:
--   Derakhshan, Golrezaei, Paes Leme, LP-based Approximation for Personalized Reserve Prices, arXiv:1905.01526v5, p. 11, Lemma 5.3 and Problem (10)

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

namespace ReserveLP.ProLPR

theorem lemma_5_3 {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B)
    (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) (hopt : LPOptimal D s q) :
    ∀ a : A, ∀ t : ℝ, t ≤ secondBid D a →
      profileMassGe D s a t - probRevGe D q a t ≤ cOPT (Fintype.card B) := by sorry

end ReserveLP.ProLPR
