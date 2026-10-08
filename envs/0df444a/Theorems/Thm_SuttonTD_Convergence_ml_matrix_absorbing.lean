-- Prove2me | Theorems.Thm_SuttonTD_Convergence_ml_matrix_absorbing
-- name    : SuttonTD.Convergence.ml_matrix_absorbing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:02:57.378575+00:00
-- url     : https://prove2.me/theorems/35258ff8-2462-4142-90f0-0886ace9afb9
-- title:
--   The maximum-likelihood matrix $\hat Q$ is absorbing: $\hat Q^n\to0$ (§4.2, p. 30)
-- statement:
--   Let a training set be given in which every nonterminal state appears, and let $[\hat Q]_{ij}=\eta_{ij}/\hat d_i$ be the maximum-likelihood estimate of the transition probabilities between nonterminal states. Then $\hat Q$ corresponds to an absorbing Markov chain:
--
--   $$\lim_{n\to\infty}\hat Q^n=0 .$$
--
--   By Theorem A.1 this guarantees that the optimal predictions $[(I-\hat Q)^{-1}\hat h]_i$ are well defined.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.2, p. 30 (PDF p. 22)

import Definitions.Def_SuttonTD_Convergence_TrainingSet
open Filter Topology

namespace SuttonTD.Convergence

/-- **`Q̂` is absorbing** (Sutton 1988, §4.2, p. 30, PDF p. 22): "Note that even though `Q̂` is an
estimated quantity, it still corresponds to some absorbing Markov chain. Thus,
`lim_{n→∞} Q̂ⁿ = 0`." For a training set in which every nonterminal state of `N` appears
(`N = N̂`), the maximum-likelihood matrix `[Q̂]_ij = η_ij / d̂_i` satisfies `Q̂ⁿ → 0`.

Formalization Note: the hypothesis that every state appears makes `N` the paper's `N̂` and keeps
the division by `d̂_i` away from `0`. -/
theorem ml_matrix_absorbing {N : Type*} [Fintype N] [DecidableEq N] {S : ℕ}
    (D : TrainingSet N S) (happ : ∀ i, 0 < D.visits i) :
    Tendsto (fun n : ℕ => D.Qhat ^ n) atTop (𝓝 0) := by sorry

end SuttonTD.Convergence
