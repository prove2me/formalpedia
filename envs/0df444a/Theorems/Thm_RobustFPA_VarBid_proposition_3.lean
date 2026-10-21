-- Prove2me | Theorems.Thm_RobustFPA_VarBid_proposition_3
-- name    : RobustFPA.VarBid.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:39.073835+00:00
-- url     : https://prove2.me/theorems/5461fdbf-de6e-4433-8888-58081a418691
-- title:
--   Proposition 3 (corrected, $G$ uniform) — $X \ne \emptyset$, a minimax loss bid exists, and it lies in $X$ and minimizes the too-high loss on $X$
-- statement:
--   Let $n \ge 2$, $0 < \tau < 1$, $0 \le L < v_1$, and $G$ uniform on $[L, v_1]$. Let
--   $$
--   X = \Bigl\{ b \in [L, v_1] : \sup_{\hat h \in [L,b]} u^+(\hat h) - u^+(b) = \sup_{\hat h > b} u^+(\hat h) - u^-(b) \Bigr\}
--   $$
--   be the set of bids at which the maximal losses of bidding too high and too low coincide. Then:
--
--   1. $X$ is nonempty;
--   2. a minimax loss bid for $\mathcal B_{\tau,G}$ exists;
--   3. every minimax loss bid $b_1^*$ lies in $X$ and minimizes the maximal loss of bidding too high on $X$:
--   $$
--   b_1^* \in \arg\min_{b \in X}\ \sup_{\hat h \in [L,b]} u^+(\hat h) - u^+(b).
--   $$
--
--   The minimax loss bid is defined from the loss over the whole ambiguity set (not from $X$); the proposition locates it among the equalizers of the two maximal losses.
--
--   **Formalization Note.** Existence of a minimax bid and $X \ne \emptyset$ are part of the paper's proof (p. 48, "It remains to be shown that X is non-empty and a minimax bid exists") and are included. The ambiguity set is the corrected one. The paper states the proposition for a general $G$; here $G$ is uniform. For general $G$ the claim that the minimax bid lies in $X$ fails: numerically, for continuous piecewise-linear $G$ with full support on $[0,1]$, the minimizer of $\max\{\text{too-high}, \text{too-low}\}$ can sit where the two differ.
-- source:
--   Kasberger & Schlag, Robust Bidding in First-Price Auctions, SSRN 3044438 (version of 3 Sep 2022), pp. 22–23, Proposition 3 (proof: Appendix B.3, pp. 48–49); posed for the corrected B_{τ,G} and G uniform

import Mathlib
import Definitions.Def_RobustFPA_VarBid_Model
import Definitions.Def_RobustFPA_VarBid_AmbiguitySet
import Definitions.Def_RobustFPA_VarBid_ClosedForms

namespace RobustFPA.VarBid

theorem proposition_3 (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v) :
    (equalizerSet n τ L v).Nonempty ∧
    (∃ b, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b) ∧
    ∀ b, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b →
      b ∈ equalizerSet n τ L v ∧
      ∀ b' ∈ equalizerSet n τ L v, tooHigh n τ L v b ≤ tooHigh n τ L v b' := by sorry

end RobustFPA.VarBid
