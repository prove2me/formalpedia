-- Prove2me | Theorems.Thm_ReusablePricing_DPCB_batch_error_sq
-- name    : ReusablePricing.DPCB.batch_error_sq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:06.951998+00:00
-- url     : https://prove2.me/theorems/7ff3f8d8-6e6f-4657-86cd-f7edfbe76137
-- title:
--   EC.4 Step 2, ec13 — E[(Σ_{s∈𝒯_k^b} Δ^s_k)²] ≤ m_k for every batch of DPC-B
-- statement:
--   In the general setting of Section 6 (model facts only), fix any parameters $m$, $\epsilon$, $\underline{n}$ of DPC-B$(m,\epsilon)$ and a valid batch partition, so that each batch $\mathcal{T}_k^b$ contains exactly $m_k$ periods with $\lambda^{t,D}_k > 0$. Then for every type $k$ and every batch $b \in [1, B_k]$, the demand errors $\Delta^s_k = D^s_k - \lambda^s_k$ satisfy
--   $$
--   \mathbf{E}\Bigl[\Bigl(\sum_{s \in \mathcal{T}_k^b} \Delta^s_k\Bigr)^2\Bigr] \le m_k .
--   $$
--
--   Step 2 of the proof of Theorem 3 uses this bound on the second-order Taylor term to obtain the $2\Psi/m_k$ part of the loss.
--
--   **Formalization Note** The statement holds for any $\epsilon$, $m$ and $\underline{n}$; none of the standing assumptions beyond the model facts is needed.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. ec13, Step 2 of the proof of Theorem 3 (the fact E[(Σ_{s∈𝒯_k^b} Δ^s_k)²] ≤ m_k)

import Mathlib
import Definitions.Def_ReusablePricing_DPCB_Events

open Finset

namespace ReusablePricing.DPCB

open General

/-- Step 2 of EC.4 (ec13): for every type `k` and every batch `b ∈ [1, B_k]`, the batch error
sum has second moment at most `m_k`: `E[(∑_{s ∈ 𝒯_k^b} Δ^s_k)²] ≤ m_k`. -/
theorem batch_error_sq (P : General) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ)
    (β : Fin P.K → ℕ → ℕ) (B : Fin P.K → ℕ)
    (hP : P.ModelFacts) (hbat : P.BatchesValid m β B) :
    ∀ k, ∀ b ∈ Icc 1 (B k),
      P.expect nl m ε β (fun ω => (∑ s ∈ P.batch β k b, P.err nl m ε β s ω k) ^ 2) ≤ (m k : ℝ) := by sorry

end ReusablePricing.DPCB
