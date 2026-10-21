-- Prove2me | Theorems.Thm_RobustFPA_VarBid_equalizerSet_eq
-- name    : RobustFPA.VarBid.equalizerSet_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:36.907616+00:00
-- url     : https://prove2.me/theorems/05be7290-715f-4ed8-a1f0-c6149f96bff9
-- title:
--   Proof of Proposition 4, p. 49 — $X$ is exactly the set of solutions of Equation (3) in $[\max\{L,\tilde b\}, v_1]$
-- statement:
--   Let $n \ge 2$, $0 < \tau < 1$ and $L < v$, with $G$ uniform on $[L, v]$. The set $X$ of Proposition 3 consists exactly of the bids in $[\max\{L,\tilde b\}, v]$ that solve Equation (3):
--   $$
--   X = \Bigl\{ b : \max\{L,\tilde b\} \le b \le v,\ \ u^+(\max\{L,\tilde b\}) - u^+(b) = u^+(b) - u^-(b) \Bigr\}.
--   $$
--   In particular no bid in $[L, \max\{L, \tilde b\})$ equalizes the two maximal losses.
--
--   On $[\max\{L,\tilde b\}, v]$ the maximal loss of bidding too high is $u^+(\max\{L,\tilde b\}) - u^+(b)$ and that of bidding too low is $u^+(b) - u^-(b)$; below the peak the too-high loss vanishes while the too-low loss is positive. This is the step that turns Proposition 3 into Equation (3).
--
--   **Formalization Note.** Both sides are sets of reals; $X$ is defined by the two suprema of Proposition 3, not by Equation (3), so the identity has content.
-- source:
--   Kasberger & Schlag, Robust Bidding in First-Price Auctions, SSRN 3044438 (version of 3 Sep 2022), p. 49 (Appendix B.4, proof of Proposition 4, after Lemma 2)

import Mathlib
import Definitions.Def_RobustFPA_VarBid_ClosedForms

namespace RobustFPA.VarBid

theorem equalizerSet_eq (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    equalizerSet n τ L v = {b | peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b} := by sorry

end RobustFPA.VarBid
