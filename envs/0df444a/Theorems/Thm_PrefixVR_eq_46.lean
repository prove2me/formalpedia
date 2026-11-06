-- Prove2me | Theorems.Thm_PrefixVR_eq_46
-- name    : PrefixVR.eq_46
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:42.437483+00:00
-- url     : https://prove2.me/theorems/95d77b48-181d-481b-91c9-1601b68de6aa
-- title:
--   Eq. (46) — the random output averages the iterates
-- statement:
--   Run Algorithm 1 with horizon $T\ge1$, any stepsize and any initial point, with output index $\tau$ uniform on $[T]$ and independent of the estimator samples. Since the trajectory does not use $\tau$,
--   $$
--   \mathbb E\,\|\nabla f(x_\tau)\|^2=\sum_{t=1}^T\mathbb P(\tau=t)\,\mathbb E\big[\|\nabla f(x_t)\|^2\,\big|\,\tau=t\big]=\frac1T\sum_{t=1}^T\mathbb E\|\nabla f(x_t)\|^2 .\qquad(46)
--   $$
--   The statement is made for the returned point $x_{\mathrm{out}}$ of the run and for every real function $\Phi$ of the point in place of $\|\nabla f(\cdot)\|^2$:
--   $$
--   \mathbb E\,\Phi(x_{\mathrm{out}})=\frac1T\sum_{t=1}^T\mathbb E\,\Phi(x_t).
--   $$
--
--   It converts the averaged bound (45) into a bound for the single returned point.
--
--   **Formalization Note** The expectation is over the output index and all draws; $x_{\mathrm{out}}$ is the point saved by the run at $t=\tau$.
--
--   Differences from the source:
--   - generalization: Φ = ‖∇f(·)‖² → every real function Φ of the point; reason: the identity uses only that τ is uniform and unused by the trajectory; Φ = ‖∇f‖² gives (46)
--   - generalization: the component gradients ∇fᵢ and η > 0 → arbitrary maps g i and any real η; reason: the identity does not use them
--   - encoding: the expectation over the estimator samples of the run of Algorithm 1 → the uniform average over the finite sample space Sample n T (output index τ and the draws (j_t, i_t) of updates t ≤ T, with one-point or unused dummy draws where the paper draws nothing), for a horizon T containing every time in the statement; reason: independent uniform draws on finite sets have the uniform product law; unused coordinates and later draws change no expectation of quantities up to the stated times
--   - encoding: components i ∈ [n] = {1, …, n} → Fin n, paper index i is i − 1, with NeZero n; reason: Lean convention; n ≥ 1 is the paper's standing setting of a finite sum
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), App. C, Eq. (46), p.16 (PDF p.16)

import Mathlib
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Sample
import Definitions.Def_PrefixVR_run

namespace PrefixVR

/-- **The random output averages the iterates, (46).** Jiang, Wang, Yang, Li, Zhang (manuscript,
sha256 ed33106a…), App. C, Eq. (46), p.16: "The trajectory does not use τ to choose its iterates.
Thus τ is independent of (x₁, …, x_T), and
𝔼‖∇f(x_τ)‖² = ∑_{t=1}^T ℙ(τ = t) 𝔼[‖∇f(x_t)‖² | τ = t] = (1/T) ∑_{t=1}^T 𝔼‖∇f(x_t)‖²."

Stated for the output `x_out` of Algorithm 1 with horizon `T ≥ 1` (any maps `g`, stepsize `η`,
initial point `x₁`) and every real function `Φ` of the point, in particular `Φ = ‖∇f(·)‖²`.

**Formalization Note.** Expectations are over `Sample n T` (output index and all draws);
`output` is the saved point of the run. -/
theorem eq_46 {n d : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (η : ℝ)
    (x₁ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (hT : 1 ≤ T) (Φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    expect (fun ω : Sample n T => Φ (output g η x₁ ω))
      = (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, expect (fun ω : Sample n T => Φ (xIter g η x₁ ω t)) := by sorry

end PrefixVR
