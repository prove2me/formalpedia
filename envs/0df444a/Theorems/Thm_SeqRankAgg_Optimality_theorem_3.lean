-- Prove2me | Theorems.Thm_SeqRankAgg_Optimality_theorem_3
-- name    : SeqRankAgg.Optimality.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:38.736495+00:00
-- url     : https://prove2.me/theorems/683524dc-9805-4e18-b4e7-2ac98ff73fc2
-- title:
--   Theorem 3, p. 13 — asymptotic sample-size upper bound
-- statement:
--   Assume A1–A5 and A7. For either stopping rule $T_i$, let a family of adaptive pair-selection rules satisfy A6 and A8. With $\mathbb E_\rho t_c(\Theta)=\int_W |\log c|D(\theta)^{-1}\rho(\theta)\,d\theta$,
--
--   $$
--   \limsup_{c\downarrow0}\frac{\mathbb E T_i}{\mathbb E_\rho t_c(\Theta)}\le1,\qquad i=1,2.
--   $$
--
--   This bounds the comparison-cost part of the Bayes risk for selection rules that explore enough and track a max–min allocation.
--
--   **Formalization Note** The Lean statement uses eventual $1+\varepsilon$ upper bounds. A6 is an almost-sure lower bound under each true parameter; A8 is a uniform limit over all finite histories after the first round. Both concern the cost-indexed family of selection rules.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, p. 13, Theorem 3

import Mathlib
import Definitions.Def_SeqRankAgg_Optimality_Model

open MeasureTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

theorem theorem_3 {m : ℕ} (hm : 1 ≤ m) (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (hA1 : A1 ρ) (hA2 : A2 ρ) (hA3 : A3 M ρ)
    (hA4 : A4 M ρ) (hA5 : A5 ρ) (hA7 : A7 M ρ)
    (αh : ℝ) (hαh : 0 < αh ∧ αh < 1)
    (θhat : (n : ℕ) → BanditAlgorithm.BanditHistory (numPairs m) n → (Fin m → ℝ))
    (hθhat : IsMLESelector M ρ θhat)
    (lamStar : (Fin m → ℝ) → Fin (numPairs m) → ℝ)
    (hLam : IsMaxMinSelector M ρ lamStar) (i : Fin 2)
    (Afam : ℝ → BanditAlgorithm.BanditPolicy (numPairs m))
    (hA6 : A6 M ρ Afam) (hA8 : A8 θhat lamStar Afam)
    (πfam : ℝ → Policy m)
    (hπ : IsGeneralFamily M ρ θhat αh i Afam πfam) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        expectedT M ρ (πfam c) ≤ ENNReal.ofReal (1 + ε) * Etc M ρ c := by sorry

end SeqRankAgg.Optimality
