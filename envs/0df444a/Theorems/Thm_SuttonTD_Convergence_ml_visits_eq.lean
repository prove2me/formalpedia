-- Prove2me | Theorems.Thm_SuttonTD_Convergence_ml_visits_eq
-- name    : SuttonTD.Convergence.ml_visits_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:03:05.920024+00:00
-- url     : https://prove2.me/theorems/63d4c84f-e22d-48b9-802c-80c0737a2838
-- title:
--   $\hat d^\top=\hat\mu^\top(I-\hat Q)^{-1}$ for a training set (§4.2, p. 31)
-- statement:
--   Let a training set be given in which every nonterminal state appears. Let $\hat d_i$ be the number of times $i$ appears, $[\hat\mu]_i$ the number of sequences beginning in $i$, and $\hat Q$ the maximum-likelihood transition matrix. Then
--
--   $$\hat d^\top=\hat\mu^\top(I-\hat Q)^{-1}.$$
--
--   This is the analogue of (7) needed to carry the proof of Theorem 2 over to Theorem 3.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.2, p. 31 (PDF p. 23)

import Definitions.Def_SuttonTD_Convergence_TrainingSet
open Matrix

namespace SuttonTD.Convergence

/-- **`d̂ᵀ = μ̂ᵀ(I − Q̂)⁻¹`** (Sutton 1988, §4.2, p. 31, PDF p. 23): for a training set in which
every nonterminal state appears, the visit counts `d̂_i`, the start counts `[μ̂]_i` and the
maximum-likelihood matrix `Q̂` satisfy `d̂ᵀ = μ̂ᵀ(I − Q̂)⁻¹` (counts cast to `ℝ`). -/
theorem ml_visits_eq {N : Type*} [Fintype N] [DecidableEq N] {S : ℕ}
    (D : TrainingSet N S) (happ : ∀ i, 0 < D.visits i) :
    (fun i => (D.visits i : ℝ)) = (fun i => (D.starts i : ℝ)) ᵥ* (1 - D.Qhat)⁻¹ := by sorry

end SuttonTD.Convergence
