-- Prove2me | Theorems.Thm_TradingFavors_Existence_lemma_4
-- name    : TradingFavors.Existence.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:23.43429+00:00
-- url     : https://prove2.me/theorems/102905c2-8b2f-46ff-b058-5a10f770b714
-- title:
--   Lemma 4, p. 16 (PDF 16) — σᴸ is a TFE iff σᴸ⁻¹ is and (14) holds (TFE on the core region)
-- statement:
--   Assume the standing assumptions and let $L\ge1$. Then $\sigma^L$ is a TFE on its core region $\{0,\dots,L\}$ if and only if $\sigma^{L-1}$ is a TFE on its core region $\{0,\dots,L-1\}$ and
--   $$
--   \pi_1(0,1,L-1\mid\sigma^L)<\pi_1(1,1,L\mid\sigma^L)-l_1\quad\text{and}\quad\pi_2(0,1,1\mid\sigma^L)<\pi_2(1,1,0\mid\sigma^L)-l_2. \tag{14}
--   $$
--   Here $\pi_2(0,1,1\mid\sigma^L)$ is firm 2's payoff at $x_2=0$, $x_1=1$, $k=1$.
--
--   Extending the core region by one favor is an equilibrium exactly when each firm wants to grant the additional favor; in particular larger core regions are harder to sustain.
--
--   **Formalization Note** "TFE" is read as condition (4) on the core region, a disclosed repair: under the literal Definition 1 (all $k\in\mathbb Z$), $\sigma^L$ with $L\ge1$ is never a TFE at the paper's own Table 2 parameters, because firm 1 strictly prefers to accept at $k=-1$. With the core reading, Tables 2 and 3 are reproduced exactly. `L - 1` is natural-number subtraction, guarded by $1\le L$.
-- source:
--   Hu & Caldentey, Trust and Reciprocity in Firms’ Capacity Sharing, SSRN 4348127 (version of February 6, 2023), p. 16 (PDF 16), Lemma 4, eq. (14); proof pp. A6–A8 (PDF 36–38)

import Mathlib
import Definitions.Def_TradingFavors_Existence_Model

namespace TradingFavors.Existence

theorem lemma_4 (θ : Params) (hθ : θ.Standing) (L : ℕ) (hL : 1 ≤ L) :
    IsCoreTFE θ L ↔
      IsCoreTFE θ (L - 1) ∧
        (pi1 θ (sigmaL L) 0 1 ((L : ℤ) - 1) < pi1 θ (sigmaL L) 1 1 (L : ℤ) - θ.l1 ∧
         pi2 θ (sigmaL L) 0 1 1 < pi2 θ (sigmaL L) 1 1 0 - θ.l2) := by sorry

end TradingFavors.Existence
