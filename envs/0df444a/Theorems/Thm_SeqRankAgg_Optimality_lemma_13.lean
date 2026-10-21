-- Prove2me | Theorems.Thm_SeqRankAgg_Optimality_lemma_13
-- name    : SeqRankAgg.Optimality.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:35.811571+00:00
-- url     : https://prove2.me/theorems/803fd8cf-7794-4e92-9f23-fd302aad54b3
-- title:
--   Lemma 13, p. 38 — information at the least distinguishable alternative
-- statement:
--   Let $t\ge1$, let $\theta\in W$, and let each of the first $t$ comparison allocations $\lambda_n$ belong to the probability simplex over pairs. Choose $\theta_t^*$ in $W$ with a different ranking from $\theta$ that minimizes the cumulative allocated divergence over such alternatives. Then
--
--   $$
--   \sum_{n=1}^{t}\sum_{i<j}\lambda_n^{i,j}D^{i,j}(\theta\|\theta_t^*)\le tD(\theta).
--   $$
--
--   This relates the hardest alternative for an adaptive sequence of allocations to the paper’s single-stage max–min information value. The minimizer is specified by its full optimization property, not treated as an unrelated parameter.
--
--   **Formalization Note** The finite index `Fin t` represents the paper’s stages $1,\ldots,t$. The theorem carries A1–A5, the standing assumptions of the lower-bound argument.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, p. 38, Lemma 13; p. 22, (6.6)

import Mathlib
import Definitions.Def_SeqRankAgg_Optimality_Model

open MeasureTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

theorem lemma_13 {m : ℕ} (hm : 1 ≤ m) (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (hA1 : A1 ρ) (hA2 : A2 ρ) (hA3 : A3 M ρ)
    (hA4 : A4 M ρ) (hA5 : A5 ρ)
    (θ : Fin m → ℝ) (hθ : θ ∈ W ρ) (t : ℕ) (ht : 1 ≤ t)
    (wgt : Fin t → Fin (numPairs m) → ℝ)
    (hwgt : ∀ n, wgt n ∈ simplex (numPairs m))
    (θstar : Fin m → ℝ) (hstar : θstar ∈ W ρ ∧ ¬ SameRank θstar θ)
    (hmin : ∀ θ' ∈ {θ' ∈ W ρ | ¬ SameRank θ' θ},
      (∑ n : Fin t, ∑ a : Fin (numPairs m),
        wgt n a * Dij M (pairOf m a) θ θstar) ≤
      (∑ n : Fin t, ∑ a : Fin (numPairs m),
        wgt n a * Dij M (pairOf m a) θ θ')) :
    (∑ n : Fin t, ∑ a : Fin (numPairs m),
      wgt n a * Dij M (pairOf m a) θ θstar) ≤ (t : ℝ) * Dfun M ρ θ := by sorry

end SeqRankAgg.Optimality
