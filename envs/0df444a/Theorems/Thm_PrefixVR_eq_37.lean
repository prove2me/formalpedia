-- Prove2me | Theorems.Thm_PrefixVR_eq_37
-- name    : PrefixVR.eq_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:47.208194+00:00
-- url     : https://prove2.me/theorems/a942b804-4d9b-4609-8692-d7016b627493
-- title:
--   Eq. (37) — one step of the active recursion
-- statement:
--   Suppose condition (2) holds with constant $\delta$, and run Algorithm 1 with stepsize $\eta$ from $x_1$. Write $e_t=v_t-\nabla f(x_t)$ and $S_t=\mathbb E\|x_{t+1}-x_t\|^2$. At every update $t$ whose cycle position $r=t-\lfloor (t-1)/n\rfloor n$ satisfies $r<n$,
--   $$
--   \mathbb E\|e_{t+1}\|^2\le\mathbb E\|e_t\|^2+\delta^2S_t .\qquad(37)
--   $$
--   Stated for every update $1\le t\le T$ of a run with horizon $T$, every stepsize and every initial point; the expectation is over all draws.
--
--   Between two cycle replacements the active estimate accumulates one sampled difference per update, and (37) says each costs at most $\delta^2S_t$ in mean square.
--
--   **Formalization Note** The maps $g_i$ stand for $\nabla f_i$ and $\nabla f$ for their average; no smoothness is assumed.
--
--   Differences from the source:
--   - generalization: the component gradients ∇fᵢ of differentiable fᵢ, with ∇f their average in (2) → arbitrary maps g i : ℝᵈ → ℝᵈ satisfying (2) with ∇f replaced by the average (1/n)∑ g i; reason: the statement and its proof use only (2); taking g i = ∇fᵢ, whose average is ∇f, gives the source's statement
--   - generalization: stepsize η > 0 (input of Algorithm 1) → any real η; reason: the bound holds for every η; restricting to η > 0 gives the source's statement
--   - encoding: the expectation over the estimator samples of the run of Algorithm 1 → the uniform average over the finite sample space Sample n T (output index τ and the draws (j_t, i_t) of updates t ≤ T, with one-point or unused dummy draws where the paper draws nothing), for a horizon T containing every time in the statement; reason: independent uniform draws on finite sets have the uniform product law; unused coordinates and later draws change no expectation of quantities up to the stated times
--   - encoding: components i ∈ [n] = {1, …, n} → Fin n, paper index i is i − 1, with NeZero n; reason: Lean convention; n ≥ 1 is the paper's standing setting of a finite sum
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), App. B, "Error of the active estimator", Eq. (37), p.14 (PDF p.14)

import Mathlib
import Definitions.Def_PrefixVR_Variation
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Sample
import Definitions.Def_PrefixVR_run

namespace PrefixVR

/-- **One step of the active recursion, (37).** Jiang, Wang, Yang, Li, Zhang (manuscript, sha256
ed33106a…), App. B, "Error of the active estimator", Eq. (37), p.14: "Taking expectation gives,
at each update with r < n, 𝔼‖e_{t+1}‖² ≤ 𝔼‖e_t‖² + δ² S_t", where `e_t := v_t − ∇f(x_t)` and
`S_t = 𝔼‖x_{t+1} − x_t‖²`.

Stated for Algorithm 1 with horizon `T`, every stepsize `η` and initial point `x₁`, for every
update `1 ≤ t ≤ T` whose cycle position `r = t − ⌊(t−1)/n⌋ n` is `< n`.

**Formalization Note.** `g i` stands for `∇fᵢ`, (2) is `Variation g δ` and `∇f` is the average
`gradAvg g`; no smoothness is assumed. The expectation is over `Sample n T`; `S_t` is
`moveEnergy`. -/
theorem eq_37 {n d : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
    (hvar : Variation g δ) (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    ∀ t : ℕ, 1 ≤ t → t ≤ T → cyclePos n t < n →
      expect (fun ω : Sample n T =>
          ‖vIter g η x₁ ω (t + 1) - gradAvg g (xIter g η x₁ ω (t + 1))‖ ^ 2)
        ≤ expect (fun ω : Sample n T => ‖vIter g η x₁ ω t - gradAvg g (xIter g η x₁ ω t)‖ ^ 2)
          + δ ^ 2 * moveEnergy g η x₁ T t := by sorry

end PrefixVR
