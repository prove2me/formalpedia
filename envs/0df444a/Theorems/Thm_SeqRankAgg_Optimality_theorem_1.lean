-- Prove2me | Theorems.Thm_SeqRankAgg_Optimality_theorem_1
-- name    : SeqRankAgg.Optimality.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:27.191858+00:00
-- url     : https://prove2.me/theorems/e43b76fd-aea2-41a7-b3b6-11e86f590923
-- title:
--   Theorem 1, p. 12 — asymptotic lower bound on optimal Bayes risk
-- statement:
--   Under Assumptions A1–A5, let $V_c^*(\rho)$ be the infimum of Bayes risk over every admissible sequential ranking policy, and let $\mathbb E_\rho t_c(\Theta)=\int_W t_c(\theta)\rho(\theta)\,d\theta$. As the positive comparison cost $c$ tends to zero,
--
--   $$
--   \liminf_{c\downarrow0}\frac{V_c^*(\rho)}{c\,\mathbb E_\rho t_c(\Theta)}\ge1.
--   $$
--
--   This is the benchmark against which both proposed policies are compared.
--
--   **Formalization Note** The Lean statement uses the equivalent eventual $1-\varepsilon$ lower bounds. Nonnegative extended reals retain infinite costs and nonterminating policies. The infimum includes all stopping times and terminal rankings that are measurable when stopped.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, p. 12, Theorem 1

import Mathlib
import Definitions.Def_SeqRankAgg_Optimality_Model

open MeasureTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

theorem theorem_1 {m : ℕ} (hm : 1 ≤ m) (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (hA1 : A1 ρ) (hA2 : A2 ρ) (hA3 : A3 M ρ)
    (hA4 : A4 M ρ) (hA5 : A5 ρ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ENNReal.ofReal (1 - ε) * (ENNReal.ofReal c * Etc M ρ c) ≤
          optRisk M ρ c := by sorry

end SeqRankAgg.Optimality
