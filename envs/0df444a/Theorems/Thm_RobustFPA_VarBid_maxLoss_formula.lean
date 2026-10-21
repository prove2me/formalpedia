-- Prove2me | Theorems.Thm_RobustFPA_VarBid_maxLoss_formula
-- name    : RobustFPA.VarBid.maxLoss_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:35.633984+00:00
-- url     : https://prove2.me/theorems/9775f163-33ae-4a9c-a67d-06aa19cb7764
-- title:
--   §6.2, p. 22 — maximal loss = max(too-high loss, too-low loss) for bids in $[L, v_1]$
-- statement:
--   Let $n \ge 2$, $0 < \tau < 1$, $0 \le L < v_1$, $G$ uniform on $[L, v_1]$, and $u^+$, $u^-$ as in the ClosedForms file. For every bid $b \in [L, v_1]$, the maximal loss over the (corrected) ambiguity set $\mathcal B_{\tau,G}$ is
--   $$
--   \sup_{B \in \mathcal B_{\tau,G}} l(b, B \mid v_1) = \max\Bigl\{\ \sup_{\hat h \in [L,b]} u^+(\hat h) - u^+(b),\ \ \sup_{\hat h > b} u^+(\hat h) - u^-(b)\Bigr\}.
--   $$
--   The first term is the maximal loss of bidding too high (the best response lies below $b$), the second the maximal loss of bidding too low.
--
--   This is the computation of §6.2 that turns the minimax problem into a one-dimensional comparison of two explicit functions; Proposition 3 is stated in these terms.
--
--   **Formalization Note.** The page writes the first supremum over $\hat h < b_1$; Proposition 3 writes it over $\hat h \in [L, b]$, which is used here (bids below $L$ never win, and $\hat h = b$ contributes $0$). The ambiguity set is the corrected one, and $G$ is uniform.
-- source:
--   Kasberger & Schlag, Robust Bidding in First-Price Auctions, SSRN 3044438 (version of 3 Sep 2022), p. 22, §6.2 (maximal losses of bidding too high and too low); posed for the corrected B_{τ,G} and G uniform

import Mathlib
import Definitions.Def_RobustFPA_VarBid_Model
import Definitions.Def_RobustFPA_VarBid_AmbiguitySet
import Definitions.Def_RobustFPA_VarBid_ClosedForms

namespace RobustFPA.VarBid

theorem maxLoss_formula (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v) (b : ℝ) (hLb : L ≤ b) (hbv : b ≤ v) :
    maxLoss v b (varBidSet n τ L (uniformG L v)) = max (tooHigh n τ L v b) (tooLow n τ L v b) := by sorry

end RobustFPA.VarBid
