-- Prove2me | Theorems.Thm_ReserveLP_ProLPR_lemma_4_3
-- name    : ReserveLP.ProLPR.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:22.932468+00:00
-- url     : https://prove2.me/theorems/bb6cc352-69e7-454b-9170-ce5d04eb471b
-- title:
--   Lemma 4.3, p. 8 — the Profile-LP value is an upper bound on ESP⋆
-- statement:
--   Consider a data-set of bids $\beta_{a,b}\ge 0$ with the two auxiliary zero-bid buyers. Let $(s^\star,q^\star)$ be an optimal solution of Profile-LP. Then every nonnegative reserve vector $r\in\mathbb R_{\ge0}^{\mathsf B}$ satisfies
--
--   $$\mathrm{Rev}(r)=\sum_{a\in\mathsf A}\mathrm{Rev}_a(r)\ \le\ \sum_{a\in\mathsf A}\sum_{p\in\mathcal P_a}s^\star_{a,p}\,\mathrm{Rev}_a(p).$$
--
--   Equivalently, $\mathsf{ESP}^\star\le$ Profile-LP. So the LP is a relaxation of the eager reserve-pricing problem, and its optimal value is the benchmark the rounding algorithm is measured against.
--
--   **Formalization Note.** $\mathsf{ESP}^\star$ is a maximum over reserve vectors. Instead of a supremum, the statement quantifies over every reserve vector. The paper writes $r\in\mathbb R^n$ and argues with an optimal $r^\star\in\mathsf R^n$, "without loss of generality". Here every $r\ge0$ is covered. A negative reserve clears the same buyers as reserve $0$, but under the p. 5 formula it would let a lone winner pay a negative price, so reserves are taken nonnegative.
-- source:
--   Derakhshan, Golrezaei, Paes Leme, LP-based Approximation for Personalized Reserve Prices, arXiv:1905.01526v5, p. 8, Lemma 4.3

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

namespace ReserveLP.ProLPR

theorem lemma_4_3 {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B)
    (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) (hopt : LPOptimal D s q) :
    ∀ r : B → ℝ, (∀ b, 0 ≤ r b) → rev D r ≤ LPObj D s := by sorry

end ReserveLP.ProLPR
