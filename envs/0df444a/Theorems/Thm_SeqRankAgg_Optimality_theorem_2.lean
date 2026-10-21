-- Prove2me | Theorems.Thm_SeqRankAgg_Optimality_theorem_2
-- name    : SeqRankAgg.Optimality.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:38.559082+00:00
-- url     : https://prove2.me/theorems/7200e99a-585b-4e0f-9c81-5e8e126f3028
-- title:
--   Theorem 2, p. 12 — expected Kendall loss is O(c)
-- statement:
--   Assume A1–A5 and A7. For either generalized likelihood ratio stopping rule $T_i$, use any adaptive pair-selection family satisfying A6 and report the ranking of the maximum likelihood estimator at stopping. Then
--
--   $$
--   \mathbb E L_K(R_i)=O(c)\qquad(c\downarrow0),\quad i=1,2.
--   $$
--
--   This bounds the ranking-error part of each policy’s Bayes risk. The assignment rule need not be the proposed ε-greedy rule.
--
--   **Formalization Note** $O(c)$ means one positive constant $K_0$ and a positive threshold $c_0$ such that the expected loss is at most $K_0c$ for every $0<c<c_0$. A6’s exploration exponent is existential, as printed. The MLE is any measurable maximizing selector.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, p. 12, Theorem 2

import Mathlib
import Definitions.Def_SeqRankAgg_Optimality_Model

open MeasureTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

theorem theorem_2 {m : ℕ} (hm : 1 ≤ m) (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (hA1 : A1 ρ) (hA2 : A2 ρ) (hA3 : A3 M ρ)
    (hA4 : A4 M ρ) (hA5 : A5 ρ) (hA7 : A7 M ρ)
    (αh : ℝ) (hαh : 0 < αh ∧ αh < 1)
    (θhat : (n : ℕ) → BanditAlgorithm.BanditHistory (numPairs m) n → (Fin m → ℝ))
    (hθhat : IsMLESelector M ρ θhat) (i : Fin 2)
    (Afam : ℝ → BanditAlgorithm.BanditPolicy (numPairs m)) (hA6 : A6 M ρ Afam)
    (πfam : ℝ → Policy m)
    (hπ : IsGeneralFamily M ρ θhat αh i Afam πfam) :
    ∃ K0 c0 : ℝ, 0 < K0 ∧ 0 < c0 ∧
      ∀ c ∈ Set.Ioo (0 : ℝ) c0,
        expectedKendall M ρ (πfam c) ≤ ENNReal.ofReal (K0 * c) := by sorry

end SeqRankAgg.Optimality
