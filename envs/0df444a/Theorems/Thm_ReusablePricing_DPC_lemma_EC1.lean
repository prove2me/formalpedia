-- Prove2me | Theorems.Thm_ReusablePricing_DPC_lemma_EC1
-- name    : ReusablePricing.DPC.lemma_EC1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:30.603009+00:00
-- url     : https://prove2.me/theorems/7ae9f6ec-2166-4494-80dd-82275b91b34f
-- title:
--   Lemma EC.1, ec5 — on 𝒢(ϵ, δ), δ = (n̲−1)(ϵ−1)/(3n̲): Cᵗ ⪰ e and λ^{t,D}_j − ϵ/n̲ ∈ (0, λ_U)
-- statement:
--   Consider the basic reusable-resource model under its standing hypotheses, run DPC($\epsilon$), and let $\Delta^s_j = D^s_j - \lambda^s_j$ be the demand error of type $j$ in period $s$. Suppose that
--   $$\epsilon \le \min\{\varphi_L, \varphi_U\}\cdot \underline n \qquad\text{and}\qquad \delta = \frac{(\underline n - 1)(\epsilon - 1)}{3\underline n}.$$
--   Then on the event $\mathcal G(\epsilon,\delta)$ that every partial sum of $\Delta_j$ inside every service cycle has absolute value below $\delta$, the following hold for all $t \in [1,T]$:
--   1. $C^t \succeq e$: every resource has at least one free unit at the beginning of period $t$;
--   2. for every $j$, $\lambda^{t,D}_j > 0$ implies $\lambda^{t,D}_j - \epsilon/\underline n \in (0, \lambda_U)$.
--
--   On this event DPC never turns off a type with positive deterministic demand, which makes its rates explicit.
--
--   **Formalization Note.** "On $\mathcal G(\epsilon,\delta)$" is read almost surely: the conclusion is claimed for every path of positive probability in the event.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. ec5, Lemma EC.1

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model
import Definitions.Def_ReusablePricing_DPC_Control

namespace ReusablePricing.DPC

open Finset

/-- Lemma EC.1 (ec5): if `ε ≤ min{φ_L, φ_U} n̲` and `δ = (n̲ - 1)(ε - 1)/(3 n̲)`, then on
`𝒢(ε, δ)` (every path of positive probability in the event), for all `t ∈ [1, T]`:
(i) `C^t ⪰ e`; (ii) `λ^{t,D}_j > 0` implies `λ^{t,D}_j - ε/n̲ ∈ (0, λ_U)`. -/
theorem lemma_EC1 (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε δ : ℝ)
    (hP : P.Standing φL φU Ψ R nl)
    (hε : ε ≤ min φL φU * nl)
    (hδ : δ = ((nl : ℝ) - 1) * (ε - 1) / (3 * nl))
    (ω : P.Path) (hω : 0 < P.pathProb ε nl ω) (hG : P.InG ε nl δ ω) :
    ∀ t ∈ Icc 1 P.T,
      (∀ i, 1 ≤ P.freeCap t ω i) ∧
      ∀ j, 0 < P.lamD t j →
        0 < P.lamD t j - ε / nl ∧ P.lamD t j - ε / nl < P.lamU := by sorry

end ReusablePricing.DPC
