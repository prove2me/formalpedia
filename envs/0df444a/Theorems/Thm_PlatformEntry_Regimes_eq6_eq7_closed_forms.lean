-- Prove2me | Theorems.Thm_PlatformEntry_Regimes_eq6_eq7_closed_forms
-- name    : PlatformEntry.Regimes.eq6_eq7_closed_forms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:40.765049+00:00
-- url     : https://prove2.me/theorems/0376fe53-a4a4-4ded-8d73-166175fca855
-- title:
--   (6)–(8), PDF p. 15 — by Lemmas 1 and 2, the seller's two-stage profits under non-entry and entry are (6) and (7)
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$ satisfy condition (5), let $c_S$ and $K$ be arbitrary, let $a + e_S > 0$, and let $(e_P, q_S, q_P)$ be an entry equilibrium of stage 2 given the carried-over value $a + e_S$. Then:
--
--   1. the seller's optimal stage-1 quantity is $q_1 = (a+e_S)/2$, i.e. it maximizes $\Pi^S_1 = q_1(a+e_S-q_1)(1-f) - c_S e_S^2$ over all $q_1$;
--   2. without entry, the seller's optimal stage-2 quantity is $q_S = (a+e_S)/2$, i.e. it maximizes (1);
--   3. the seller's two-stage profit without entry, the sum of these two optimal profits, equals (6):
--   $$\Pi^S_N(e_S) = \frac{(1-f)(a+e_S)^2}{2} - c_S e_S^2;$$
--   4. the seller's two-stage profit with entry, the optimal stage-1 profit plus the seller's stage-2 profit (3) in the entry equilibrium, equals (7):
--   $$\Pi^S_E(e_S) = \Big(\frac14 + H\Big)(1-f)(a+e_S)^2 - c_S e_S^2,$$
--   with $H$ of (8).
--
--   This ties the paper's closed forms to the game, so that the comparison of $\Pi^S_E$ and $\Pi^S_N$ in Proposition 2 is a comparison of equilibrium profits.
--
--   **Formalization Note** The stage-1 and no-entry maximizations are over all real quantities; the maximizer $(a+e_S)/2$ is positive.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), PDF p. 15, (6), (7), (8) ("by Lemmas 1 and 2, we have the following closed-form expressions")

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

namespace PlatformEntry.Regimes

theorem eq6_eq7_closed_forms (δ f β cS K a eS eP qS qP : ℝ) (hbox : InBox δ f β)
    (h5 : cond5 δ f β) (hA : 0 < a + eS) (heq : IsEntryEq δ f β K (a + eS) eP qS qP) :
    (∀ q : ℝ, stage1Seller f cS a eS q ≤ stage1Seller f cS a eS ((a + eS) / 2)) ∧
    (∀ q : ℝ, stage2SellerN f (a + eS) q ≤ stage2SellerN f (a + eS) ((a + eS) / 2)) ∧
    profitN δ f β cS a eS =
      stage1Seller f cS a eS ((a + eS) / 2) + stage2SellerN f (a + eS) ((a + eS) / 2) ∧
    profitE δ f β cS a eS =
      stage1Seller f cS a eS ((a + eS) / 2) + sellerPayoffE δ f β (a + eS) eP qS qP := by sorry

end PlatformEntry.Regimes
