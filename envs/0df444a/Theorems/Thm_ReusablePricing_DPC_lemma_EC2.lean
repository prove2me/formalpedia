-- Prove2me | Theorems.Thm_ReusablePricing_DPC_lemma_EC2
-- name    : ReusablePricing.DPC.lemma_EC2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:29.887096+00:00
-- url     : https://prove2.me/theorems/644634b0-60fe-4d1c-abc5-e3af01bb3355
-- title:
--   Lemma EC.2, ec6 — P(𝒢̄(ϵ, δ)) ≤ (2JT/n)·exp{min{maxᵢCᵢ, n}·γ² − δγ} for γ ∈ (0, 1]
-- statement:
--   Consider the basic reusable-resource model under its standing hypotheses and run DPC($\epsilon$) with $\epsilon > 0$. For every $\delta > 0$ and every $\gamma \in (0,1]$, the complement $\bar{\mathcal G}(\epsilon,\delta)$ of the event $\mathcal G(\epsilon,\delta)$ satisfies
--   $$\mathbf P\big(\bar{\mathcal G}(\epsilon,\delta)\big) \le \frac{2JT}{n}\exp\big\{\min\{\max_i C_i, n\}\cdot\gamma^2 - \delta\gamma\big\}.$$
--
--   Together with Lemma EC.1, this shows that DPC behaves like its deterministic counterpart with high probability.
--
--   **Formalization Note.** $\delta > 0$ is the page's "for some positive $\delta$" (EC.3, Step 1), and $\epsilon > 0$ is the standing range of the DPC parameter (p. 12).
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. ec6, Lemma EC.2

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model
import Definitions.Def_ReusablePricing_DPC_Control

namespace ReusablePricing.DPC

open Finset

/-- Lemma EC.2 (ec6): for `δ > 0` and every `γ ∈ (0, 1]`, under DPC(ε) with `ε > 0`,
`P(𝒢̄(ε, δ)) ≤ (2JT/n) exp{min{max_i C_i, n} γ² - δ γ}`. -/
theorem lemma_EC2 (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε δ : ℝ)
    (hP : P.Standing φL φU Ψ R nl) (hε : 0 < ε) (hδ : 0 < δ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    P.prob ε nl (fun ω => ¬ P.InG ε nl δ ω) ≤
      2 * (P.J : ℝ) * P.T / P.n * Real.exp (P.minCapN * γ ^ 2 - δ * γ) := by sorry

end ReusablePricing.DPC
