-- Prove2me | Theorems.Thm_RobustFPA_VarBid_equation3_unique
-- name    : RobustFPA.VarBid.equation3_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:37.623306+00:00
-- url     : https://prove2.me/theorems/6be3333e-46ff-4e8b-9a84-847853b5632f
-- title:
--   Proof of Proposition 4, p. 50 — Equation (3) has a unique solution in $[\max\{L,\tilde b\}, v_1]$
-- statement:
--   Let $n \ge 2$, $0 < \tau < 1$ and $L < v$. On the interval $I = [\max\{L,\tilde b\}, v]$:
--
--   1. the left-hand side of Equation (3), $b \mapsto u^+(\max\{L,\tilde b\}) - u^+(b)$, is nondecreasing;
--   2. the right-hand side, $b \mapsto u^+(b) - u^-(b)$, is strictly decreasing;
--   3. Equation (3),
--   $$
--   u^+(\max\{L,\tilde b\}) - u^+(b) = u^+(b) - u^-(b),
--   $$
--   has exactly one solution $b \in I$.
--
--   Uniqueness of the root is what makes the minimax loss bid unique in Proposition 4.
--
--   **Formalization Note.** The page's bound "$b > ((n-1)+L)/n$" is a typo for $((n-1)v+L)/n$ and is not part of the statement; only the monotonicity claims and the unique root are formalized. Strict decrease of the right-hand side uses $\tau < 1$ (p. 50, "which holds if and only if τ < 1").
-- source:
--   Kasberger & Schlag, Robust Bidding in First-Price Auctions, SSRN 3044438 (version of 3 Sep 2022), pp. 50–51 (Appendix B.4, proof of Proposition 4: uniqueness of the solution of Equation (3))

import Mathlib
import Definitions.Def_RobustFPA_VarBid_ClosedForms

namespace RobustFPA.VarBid

theorem equation3_unique (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    MonotoneOn (fun b => uPlus n τ L v (peakBid n τ L v) - uPlus n τ L v b)
      (Set.Icc (peakBid n τ L v) v) ∧
    StrictAntiOn (fun b => uPlus n τ L v b - uMinus n τ L v b) (Set.Icc (peakBid n τ L v) v) ∧
    ∃! b : ℝ, peakBid n τ L v ≤ b ∧ b ≤ v ∧ Equation3 n τ L v b := by sorry

end RobustFPA.VarBid
