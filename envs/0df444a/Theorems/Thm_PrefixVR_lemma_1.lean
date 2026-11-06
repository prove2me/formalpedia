-- Prove2me | Theorems.Thm_PrefixVR_lemma_1
-- name    : PrefixVR.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:56.625367+00:00
-- url     : https://prove2.me/theorems/ab9809fa-827e-4fe9-b632-665cdbf41a34
-- title:
--   Lemma 1 — the finite-window error bound (8)–(9)
-- statement:
--   Suppose condition (2) holds with constant $\delta$. Initialize $v_1=\nabla f(x_1)$ and update the estimators by (5)–(7) with the sampling rules of Algorithm 1 (any stepsize $\eta$). Write
--   $$
--   e_t=v_t-\nabla f(x_t),\qquad S_t=\mathbb E\|x_{t+1}-x_t\|^2\ (t\ge1),\qquad S_t=0\ (t\le0).
--   $$
--   Then
--
--   1. for every time $t\ge1$: $\displaystyle\mathbb E\|e_t\|^2\le\delta^2\sum_{j=1}^{2n}S_{t-j}$ (8);
--   2. for every $T\ge1$: $\displaystyle\sum_{t=1}^T\mathbb E\|e_t\|^2\le2n\delta^2\sum_{t=1}^TS_t$ (9).
--
--   For a run with horizon $T$ (draws for updates $1,\dots,T$), (8) is stated for every $1\le t\le T+1$ and (9) for every $T'\le T$ in place of $T$.
--
--   This is the main invariant behind all convergence results: the estimator error is controlled by the movement in the last $2n$ updates, without any full-gradient refresh.
--
--   **Formalization Note** The maps $g_i$ stand for $\nabla f_i$ and $\nabla f$ for their average, so the run's $v_1=\frac1n\sum_i g_i(x_1)$ is $\nabla f(x_1)$; no smoothness is assumed. A window term $S_{t-j}$ with $t-j\le0$ is written as $0$ through the guard $j<t$.
--
--   Differences from the source:
--   - generalization: the component gradients ∇fᵢ of differentiable fᵢ, with ∇f their average in (2) → arbitrary maps g i : ℝᵈ → ℝᵈ satisfying (2) with ∇f replaced by the average (1/n)∑ g i; reason: the statement and its proof use only (2); taking g i = ∇fᵢ, whose average is ∇f, gives the source's statement
--   - generalization: stepsize η > 0 (input of Algorithm 1) → any real η; reason: the bound holds for every η; restricting to η > 0 gives the source's statement
--   - encoding: the expectation over the estimator samples of the run of Algorithm 1 → the uniform average over the finite sample space Sample n T (output index τ and the draws (j_t, i_t) of updates t ≤ T, with one-point or unused dummy draws where the paper draws nothing), for a horizon T containing every time in the statement; reason: independent uniform draws on finite sets have the uniform product law; unused coordinates and later draws change no expectation of quantities up to the stated times
--   - encoding: components i ∈ [n] = {1, …, n} → Fin n, paper index i is i − 1, with NeZero n; reason: Lean convention; n ≥ 1 is the paper's standing setting of a finite sum
--   - encoding: S_t := 0 for t ≤ 0 in the window sum → the guard j < t on natural-number times; reason: the same terms vanish
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §3.2, Lemma 1, Eqs. (8)–(9), p.6 (PDF p.6); proof App. B, pp.13–15

import Mathlib
import Definitions.Def_PrefixVR_Variation
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Sample
import Definitions.Def_PrefixVR_run

namespace PrefixVR

/-- **Lemma 1 (the finite-window error bound).** Jiang, Wang, Yang, Li, Zhang (manuscript, sha256
ed33106a…), Lemma 1, Eqs. (8)–(9), p.6: suppose (2) holds; initialize `v₁ = ∇f(x₁)` and update
the estimators by (5)–(7) with the sampling rules of Algorithm 1; with `e_t := v_t − ∇f(x_t)`,
`S_t := 𝔼‖x_{t+1} − x_t‖²` (`t ≥ 1`), `S_t := 0` (`t ≤ 0`):
`𝔼‖e_t‖² ≤ δ² ∑_{j=1}^{2n} S_{t−j}` (8) and `∑_{t=1}^T 𝔼‖e_t‖² ≤ 2nδ² ∑_{t=1}^T S_t` (9), for any
integer `T ≥ 1`.

Stated for Algorithm 1 run with horizon `T` (any stepsize `η`, any `x₁`): (8) for every time
`1 ≤ t ≤ T + 1` (every time whose `v_t` the run computes), and (9) for every `T' ≤ T`.

**Formalization Note.** `g i` stands for `∇fᵢ`, (2) is `Variation g δ` and `∇f` is the average
`gradAvg g`, so `v₁ = gradAvg g x₁` is the paper's initialization; no smoothness is assumed. The
window term `S_{t−j}` with `t − j ≤ 0` is `0`, written as the guard `j < t`. Expectations are over
`Sample n T`; `S_u` is `moveEnergy`. -/
theorem lemma_1 {n d : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
    (hvar : Variation g δ) (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    (∀ t : ℕ, 1 ≤ t → t ≤ T + 1 →
      expect (fun ω : Sample n T => ‖vIter g η x₁ ω t - gradAvg g (xIter g η x₁ ω t)‖ ^ 2)
        ≤ δ ^ 2 * ∑ j ∈ Finset.Icc 1 (2 * n),
            (if j < t then moveEnergy g η x₁ T (t - j) else 0)) ∧
    (∀ T' : ℕ, T' ≤ T →
      ∑ t ∈ Finset.Icc 1 T',
          expect (fun ω : Sample n T => ‖vIter g η x₁ ω t - gradAvg g (xIter g η x₁ ω t)‖ ^ 2)
        ≤ 2 * n * δ ^ 2 * ∑ t ∈ Finset.Icc 1 T', moveEnergy g η x₁ T t) := by sorry

end PrefixVR
