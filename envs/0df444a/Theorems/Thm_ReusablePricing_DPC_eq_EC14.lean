-- Prove2me | Theorems.Thm_ReusablePricing_DPC_eq_EC14
-- name    : ReusablePricing.DPC.eq_EC14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:34.891398+00:00
-- url     : https://prove2.me/theorems/b56c4070-231e-4433-800c-6c12eb23123b
-- title:
--   (EC.14), ec6 — on 𝒢(ϵ, δ), DPC(ϵ) posts λᵗ_j = λ^{t,D}_j − (ϵ/n̲)·1{λ^{t,D}_j > 0}
-- statement:
--   Under the hypotheses of Lemma EC.1, namely the standing hypotheses of the basic model, $\epsilon \le \min\{\varphi_L,\varphi_U\}\,\underline n$ and $\delta = (\underline n-1)(\epsilon-1)/(3\underline n)$, the rates posted by DPC($\epsilon$) on the event $\mathcal G(\epsilon,\delta)$ are, for every period $t \in [1,T]$ and every type $j$,
--   $$\lambda^t_j = \lambda^{t,D}_j - \frac{\epsilon}{\underline n}\,\mathbf 1\{\lambda^{t,D}_j > 0\}.$$
--
--   The projection and the turn-off of DPC are inactive on $\mathcal G(\epsilon,\delta)$. This is what Step 2 of the proof of Theorem 1 uses to compare the revenue of DPC with $J^D$.
--
--   **Formalization Note.** As in Lemma EC.1, the claim is made for every path of positive probability in $\mathcal G(\epsilon,\delta)$.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. ec6, (EC.14)

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model
import Definitions.Def_ReusablePricing_DPC_Control

namespace ReusablePricing.DPC

open Finset

/-- (EC.14), ec6: under the hypotheses of Lemma EC.1, on `𝒢(ε, δ)` (every path of positive
probability in the event) DPC(ε) posts `λ^t_j = λ^{t,D}_j - (ε/n̲) 1{λ^{t,D}_j > 0}` for all
`t ∈ [1, T]` and all `j`. -/
theorem eq_EC14 (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε δ : ℝ)
    (hP : P.Standing φL φU Ψ R nl)
    (hε : ε ≤ min φL φU * nl)
    (hδ : δ = ((nl : ℝ) - 1) * (ε - 1) / (3 * nl))
    (ω : P.Path) (hω : 0 < P.pathProb ε nl ω) (hG : P.InG ε nl δ ω) :
    ∀ t ∈ Icc 1 P.T, ∀ j,
      P.dpcRate ε nl t ω j = P.lamD t j - ε / nl * (if 0 < P.lamD t j then 1 else 0) := by sorry

end ReusablePricing.DPC
