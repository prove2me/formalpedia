-- Prove2me | Theorems.Thm_SeqRankAgg_Optimality_lemma_14
-- name    : SeqRankAgg.Optimality.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:27.311785+00:00
-- url     : https://prove2.me/theorems/531c5535-4193-4497-afaf-8fe4f7003871
-- title:
--   Lemma 14, p. 42 — information value is Lipschitz within a ranking region
-- statement:
--   For parameters $\theta,\tilde\theta\in W$ that induce the same ranking, there is a constant $\kappa_D>0$, independent of the parameters, such that
--
--   $$
--   |D(\tilde\theta)-D(\theta)|\le\kappa_D\|\tilde\theta-\theta\|.
--   $$
--
--   The result controls how the max–min information changes while the ranking remains fixed, and is used in the sample-size analysis.
--
--   **Formalization Note** The norm on $\mathbb R^{K-1}$ is the function space’s sup norm. The statement carries the standing assumptions under which the paper applies this lemma.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, p. 42, Lemma 14; p. 45, Appendix I

import Mathlib
import Definitions.Def_SeqRankAgg_Optimality_Model

open MeasureTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

theorem lemma_14 {m : ℕ} (hm : 1 ≤ m) (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (hA1 : A1 ρ) (hA2 : A2 ρ) (hA3 : A3 M ρ)
    (hA4 : A4 M ρ) (hA5 : A5 ρ) (hA7 : A7 M ρ) :
    ∃ κD : ℝ, 0 < κD ∧ ∀ θ ∈ W ρ, ∀ θ' ∈ W ρ,
      SameRank θ θ' → |Dfun M ρ θ' - Dfun M ρ θ| ≤ κD * ‖θ' - θ‖ := by sorry

end SeqRankAgg.Optimality
