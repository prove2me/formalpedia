-- Prove2me | Theorems.Thm_SuttonTD_Convergence_theorem_3
-- name    : SuttonTD.Convergence.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:03:26.073367+00:00
-- url     : https://prove2.me/theorems/f935bac7-2f7b-4ec0-a579-c9a2705c1705
-- title:
--   Theorem 3 — batch linear TD(0) converges to the maximum-likelihood (optimal) predictions
-- statement:
--   Let a training set be given in which every nonterminal state appears, and whose observation vectors $\{x_i\mid i\in\hat N\}$ are linearly independent. Then there exists $\varepsilon>0$ such that for every $\alpha$ with $0<\alpha<\varepsilon$ and every initial weight vector $w_0$, the weight vectors $w_n$ of linear TD(0) under repeated presentations of the training set, with weight updates after each complete presentation, satisfy
--
--   $$\lim_{n\to\infty}x_i^\top w_n=\bigl[(I-\hat Q)^{-1}\hat h\bigr]_i\qquad\text{for every } i\in\hat N,$$
--
--   the optimal (maximum-likelihood) predictions (8).
--
--   **Formalization Note** The set of states $N$ is the set $\hat N$ of states appearing in the training set; every sequence terminates in its own terminal state, which is built into $\hat h$. $\varepsilon$ may depend on the training set and the observation vectors.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.2, Theorem 3, p. 31 (PDF p. 23); (8), p. 30

import Definitions.Def_SuttonTD_Convergence_TrainingSet
open Filter Topology Matrix

namespace SuttonTD.Convergence

/-- **Theorem 3** (Sutton 1988, §4.2, p. 31, PDF p. 23): "For any training set whose observation
vectors `{x_i | i ∈ N̂}` are linearly independent, there exists an `ε > 0` such that, for all
positive `α < ε` and for any initial weight vector, the predictions of linear TD(0) converge,
under repeated presentations of the training set with weight updates after each complete
presentation, to the optimal predictions (8). That is, if `w_n` is the value of the weight vector
after the training set has been presented `n` times, then
`lim_{n→∞} x_iᵀw_n = [(I − Q̂)⁻¹ĥ]_i`, `∀ i ∈ N̂`."

Formalization Note: every state of `N` appears in the training set, so `N = N̂`; each sequence
terminates in its own terminal state (p. 30), which is built into `ĥ`. `ε` may depend on the
training set and the observation vectors. -/
theorem theorem_3 {N : Type*} [Fintype N] [DecidableEq N] {S : ℕ}
    (D : TrainingSet N S) (happ : ∀ i, 0 < D.visits i)
    {K : ℕ} (x : N → Fin K → ℝ) (hx : LinearIndependent ℝ x) :
    ∃ ε > 0, ∀ α : ℝ, 0 < α → α < ε → ∀ (w₀ : Fin K → ℝ) (i : N),
      Tendsto (fun n => x i ⬝ᵥ TrainingSet.presentWeights x α w₀ D n) atTop
        (𝓝 (((1 - D.Qhat)⁻¹ *ᵥ D.hhat) i)) := by sorry

end SuttonTD.Convergence
