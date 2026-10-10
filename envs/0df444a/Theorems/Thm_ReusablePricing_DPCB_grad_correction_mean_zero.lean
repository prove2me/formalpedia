-- Prove2me | Theorems.Thm_ReusablePricing_DPCB_grad_correction_mean_zero
-- name    : ReusablePricing.DPCB.grad_correction_mean_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:18.645287+00:00
-- url     : https://prove2.me/theorems/0329d33e-8ccc-45cc-8e30-29ae30c2d8c9
-- title:
--   EC.4 Step 2, ec13 — E([∇rᵗ(λ^{t,D})]ᵀ(η^t_δ ⊙ η^t_e)) = 0
-- statement:
--   In the general setting of Section 6 (model facts only), fix any parameters of DPC-B$(m,\epsilon)$. For a period $t \in [1,T]$ let $(\eta^t_e)_k = \mathbf{1}\{\lambda^{t,D}_k > 0\}$ and $(\eta^t_\delta)_k = \frac{1}{m_k}\sum_{s \in \mathcal{T}_k^{\beta_k(t)-1}} \Delta^s_k$, and let $\odot$ be the entrywise product. Then
--   $$
--   \mathbf{E}\Bigl( \bigl[\nabla r^t(\lambda^{t,D})\bigr]^\top \bigl(\eta^t_\delta \odot \eta^t_e\bigr) \Bigr) = 0 .
--   $$
--
--   The adaptive correction term therefore costs nothing to first order in expectation; Step 2 of the proof of Theorem 3 uses this to drop the linear term of the Taylor expansion.
--
--   **Formalization Note** The gradient is written through the partial derivatives $\partial r^t/\partial\lambda_k$ (the Fréchet derivative applied to the coordinate vectors). The page justifies the identity by "$\{\Delta^s_k\}$ are independent zero-mean random variables"; the errors are in fact martingale differences, since the rates depend on the past, and the identity is stated without that justification. It holds for any batch-index function and needs no assumption beyond the model facts.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. ec13, Step 2 of the proof of Theorem 3

import Mathlib
import Definitions.Def_ReusablePricing_DPCB_Events

open Finset

namespace ReusablePricing.DPCB

open General

/-- Step 2 of EC.4 (ec13): for every period `t ∈ [1, T]`,
`E([∇r^t(λ^{t,D})]ᵀ (η^t_δ ⊙ η^t_e)) = 0`, where `(η^t_δ)_k = (∑_{s ∈ 𝒯_k^{β_k(t)-1}} Δ^s_k)/m_k`
and `(η^t_e)_k = 1{λ^{t,D}_k > 0}`. -/
theorem grad_correction_mean_zero (P : General) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ)
    (β : Fin P.K → ℕ → ℕ) (hP : P.ModelFacts) :
    ∀ t ∈ Icc 1 P.T,
      P.expect nl m ε β (fun ω => ∑ k, fderiv ℝ (P.r t) (P.lamD t) (Pi.single k 1) *
        (P.etaDelta nl m ε β t ω k * P.etaE t k)) = 0 := by sorry

end ReusablePricing.DPCB
