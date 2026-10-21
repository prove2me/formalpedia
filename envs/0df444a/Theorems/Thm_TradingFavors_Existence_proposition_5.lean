-- Prove2me | Theorems.Thm_TradingFavors_Existence_proposition_5
-- name    : TradingFavors.Existence.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:18.887495+00:00
-- url     : https://prove2.me/theorems/38f70e3d-33ca-4bea-b743-7319ae623b3b
-- title:
--   Proposition 5, p. 16 (PDF 16) — a non-trivial trading-favors equilibrium exists iff (15) (TFE on the core region)
-- statement:
--   Assume the standing assumptions $\lambda_i,\mu_i,\gamma>0$, $p_i,q_i,l_i\ge0$, $q_i<p_i$. A non-trivial trading-favors equilibrium, that is, a profile $\sigma^L$ with core region $\{0,1,\dots,L\}$ of size $L\ge1$ that is a TFE on that core region, exists if and only if
--   $$
--   \beta_2q_1>\hat\rho_1(p_1-l_1)+l_1\quad\text{and}\quad\alpha_1q_2>\hat\rho_2(p_2-l_2)+l_2, \tag{15}
--   $$
--   where $\hat\rho_i=\lambda_i/(\lambda_i+\mu_i+\gamma)$ is firm $i$'s modified traffic intensity and $\alpha_1=\lambda_2[B_1^{-1}]_{4,3}$, $\beta_2=\lambda_1[B_1^{-1}]_{4,2}$ are the discounted first-passage factors of Lemma 3.
--
--   Each firm grants favors in equilibrium only if the discounted value of the favor being returned exceeds the immediate service cost plus the discounted opportunity cost of being busy. The condition is explicit in the primitives and decides whether capacity sharing without payments can be sustained at all.
--
--   **Formalization Note** Two reading choices. (i) "Non-trivial TFE with core region size $L\ge1$" ranges over the profiles $\sigma^L$, $L\ge1$: by the shift invariance of p. 15 one may take $\underline K_2=1$, and $\sigma^L$ (Definition 3) is then the bounded profile whose collaboration region equals its core $\{0,\dots,L\}$. (ii) "TFE" is condition (4) on the core region $\{0,\dots,L\}$, not at every $k\in\mathbb Z$. This is a disclosed repair: under the printed Definition 1 the statement is false. At the paper's Table 2 parameters ($p=1$, $q=0.8$, $l=0.3$, $\mu=1$, $\lambda=0.5$, $\gamma=0.001$), (15) holds ($\beta_2q_1\approx0.791>0.533$), yet firm 1's margin in (4) at $k=-1$ is $+11.26$, so no $\sigma^L$ with $L\ge1$ satisfies (4) at every $k$. The paper's proofs check (4) on the core only, and with that reading Tables 2 and 3 are reproduced exactly. The added hypotheses $\lambda_i,\mu_i>0$ make $\alpha_1,\beta_2\in(0,1)$. $\alpha_1$ and $\beta_2$ are the matrix-inverse entries, never a closed form.
-- source:
--   Hu & Caldentey, Trust and Reciprocity in Firms’ Capacity Sharing, SSRN 4348127 (version of February 6, 2023), p. 16 (PDF 16), Proposition 5, eq. (15), Definition 4; proof p. A8 (PDF 38)

import Mathlib
import Definitions.Def_TradingFavors_Existence_Model

namespace TradingFavors.Existence

theorem proposition_5 (θ : Params) (hθ : θ.Standing) :
    (∃ L : ℕ, 1 ≤ L ∧ IsCoreTFE θ L) ↔ Cond15 θ := by sorry

end TradingFavors.Existence
