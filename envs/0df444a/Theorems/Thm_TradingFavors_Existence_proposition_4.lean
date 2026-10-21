-- Prove2me | Theorems.Thm_TradingFavors_Existence_proposition_4
-- name    : TradingFavors.Existence.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:16.263514+00:00
-- url     : https://prove2.me/theorems/f38a97b1-a5b6-484c-a3cc-b171204e1cbb
-- title:
--   Proposition 4, p. 15 (PDF 15) — under σᴸ, π₁ increases and π₂ decreases in k, and payoffs grow with L (TFE on the core region)
-- statement:
--   Assume the standing assumptions and let $L\ge0$ be such that $\sigma^L$ is a TFE on its core region $\{0,\dots,L\}$. Then:
--
--   1. for every $(x_1,x_2)$, $k\mapsto\pi_1(x_1,x_2,k\mid\sigma^L)$ is nondecreasing and $k\mapsto\pi_2(x_2,x_1,k\mid\sigma^L)$ is nonincreasing on $\{0,1,\dots,L\}$;
--   2. if $\sigma^{L+1}$ is also a TFE on its core region, then for every $(x_1,x_2)$ and every $k\in\mathbb Z$
--   $$
--   \pi_1(x_1,x_2,k\mid\sigma^L)\le\pi_1(x_1,x_2,k\mid\sigma^{L+1}),\qquad \pi_2(x_2,x_1,k\mid\sigma^L)\le\pi_2(x_2,x_1,k+1\mid\sigma^{L+1}).
--   $$
--
--   Firm 1's payoff grows with the favors it has banked and firm 2's falls, and both firms gain when the collaboration region is enlarged.
--
--   **Formalization Note** "Increases"/"decreases" is stated weakly, as the proof gives it. "TFE" is read as condition (4) on the core region $\{0,\dots,L\}$ rather than at every integer: under the literal Definition 1, $\sigma^L$ with $L\ge1$ violates (4) just outside its core, and the paper's own proofs and numerics check (4) only on the core (see Proposition 5).
-- source:
--   Hu & Caldentey, Trust and Reciprocity in Firms’ Capacity Sharing, SSRN 4348127 (version of February 6, 2023), p. 15 (PDF 15), Proposition 4; proof pp. A4–A5 (PDF 34–35)

import Mathlib
import Definitions.Def_TradingFavors_Existence_Model

namespace TradingFavors.Existence

theorem proposition_4 (θ : Params) (hθ : θ.Standing) (L : ℕ) (hL : IsCoreTFE θ L) :
    (∀ x1 x2 : Fin 2,
      MonotoneOn (fun k : ℤ => pi1 θ (sigmaL L) x1 x2 k) (Set.Icc 0 (L : ℤ)) ∧
      AntitoneOn (fun k : ℤ => pi2 θ (sigmaL L) x2 x1 k) (Set.Icc 0 (L : ℤ))) ∧
    (IsCoreTFE θ (L + 1) → ∀ x1 x2 : Fin 2, ∀ k : ℤ,
      pi1 θ (sigmaL L) x1 x2 k ≤ pi1 θ (sigmaL (L + 1)) x1 x2 k ∧
      pi2 θ (sigmaL L) x2 x1 k ≤ pi2 θ (sigmaL (L + 1)) x2 x1 (k + 1)) := by sorry

end TradingFavors.Existence
