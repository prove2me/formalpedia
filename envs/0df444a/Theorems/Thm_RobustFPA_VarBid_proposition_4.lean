-- Prove2me | Theorems.Thm_RobustFPA_VarBid_proposition_4
-- name    : RobustFPA.VarBid.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:43.664708+00:00
-- url     : https://prove2.me/theorems/95ffc8ad-02ca-4c64-8aeb-38294facc9c3
-- title:
--   Proposition 4 (corrected) — for $G$ uniform the minimax loss bid is unique, solves Equation (3), has minimax loss $u^+(b^*)-u^-(b^*)$, and increases in $n$
-- statement:
--   Let $n \ge 2$ bidders, $0 < \tau < 1$, $0 \le L < v_1$, and let $G$ be uniform on $[L, v_1]$, $G(x) = (x-L)/(v_1-L)$. Let $\mathcal B_{\tau,G}$ be the (corrected) ambiguity set of variation in bidding, and let $u^+$, $u^-$, $\tilde b = v_1 - (v_1-L)/(n\tau)$ be as in the ClosedForms file. Then:
--
--   1. **Existence and uniqueness.** There is exactly one minimax loss bid $b_1^*$, i.e. exactly one $b_1^* \ge 0$ minimizing $\sup_{B \in \mathcal B_{\tau,G}} l(b_1, B \mid v_1)$ over all $b_1 \ge 0$.
--   2. **Characterization.** A bid $b$ is the minimax loss bid if and only if $b \in [\max\{L,\tilde b\}, v_1]$ and
--   $$
--   u^+(\max\{L,\tilde b\}) - u^+(b) = u^+(b) - u^-(b). \tag{3}
--   $$
--   3. **Minimax loss.** The minimax loss equals $l_1^* = u^+(b_1^*) - u^-(b_1^*)$.
--   4. **Monotonicity in $n$.** If $b_1^*$ is the minimax loss bid with $n$ bidders and $b_1^{*\prime}$ the one with $n+1$ bidders (same $\tau$, $L$, $v_1$), then $b_1^* < b_1^{*\prime}$.
--
--   This is the paper's recommended bid for variation in bidding: a closed-form, robust bid that requires only $n$, $\tau$, $L$ and $v_1$, with a guarantee on the loss against every environment in the ambiguity set.
--
--   **Formalization Note.** The minimax loss bid is defined from the loss (Model file): bids range over all $b \ge 0$, the loss is a supremum over all best responses $\bar b \ge 0$, and the maximal loss is a supremum over every distribution in $\mathcal B_{\tau,G}$, all of whose admissible unconstrained-bid laws $H$ on $[L,\infty)^{n-1}$ are included. The ambiguity set is corrected (unconstrained bids $\ge L$ and independent of who is constrained); with the printed set the proposition is false for $n \ge 3$. The range restriction in item 2 comes from p. 49 ("X only contains elements in $[\max\{L,\tilde b\}, v_1]$"). The paper differentiates in a real $n$; item 4 compares the integers $n$ and $n+1$. The hypotheses $0 < \tau < 1$ and $0 \le L < v_1$ are implicit in the paper (τ is a probability and the proof uses τ < 1 on p. 50; bids are non-negative; $G$ requires $v_1 > L$).
-- source:
--   Kasberger & Schlag, Robust Bidding in First-Price Auctions, SSRN 3044438 (version of 3 Sep 2022), pp. 23–24, Proposition 4 (proof: Appendix B.4, pp. 49–51); posed for the corrected B_{τ,G}

import Mathlib
import Definitions.Def_RobustFPA_VarBid_Model
import Definitions.Def_RobustFPA_VarBid_AmbiguitySet
import Definitions.Def_RobustFPA_VarBid_ClosedForms

namespace RobustFPA.VarBid

theorem proposition_4 (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v) :
    (∃! b : ℝ, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b) ∧
    (∀ b : ℝ, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b ↔
      (peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b)) ∧
    (∀ b : ℝ, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b →
      maxLoss v b (varBidSet n τ L (uniformG L v)) = uPlus n τ L v b - uMinus n τ L v b) ∧
    (∀ b b' : ℝ, IsMinimaxLossBid v (varBidSet n τ L (uniformG L v)) b →
      IsMinimaxLossBid v (varBidSet (n + 1) τ L (uniformG L v)) b' → b < b') := by sorry

end RobustFPA.VarBid
