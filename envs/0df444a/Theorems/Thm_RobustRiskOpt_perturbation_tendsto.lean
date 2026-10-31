-- Prove2me | Theorems.Thm_RobustRiskOpt_perturbation_tendsto
-- name    : RobustRiskOpt.perturbation_tendsto
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:53.765046+00:00
-- url     : https://prove2.me/theorems/88d90129-da25-4484-a829-51d922e3ec6a
-- title:
--   p.30 — $\varepsilon$-perturbations are $\varepsilon$-close in every metric of Assumption G
-- statement:
--   Let $(\mathcal Z,\pi)$ be one of the uncertainty models of Assumption G, with $X\in\mathcal Z$. Let $\varepsilon>0$ and let $Z$ be a random vector with $|Z(\omega)-X(\omega)|\le\varepsilon$ for all $\omega$. Then $Z\in\mathcal Z$ and
--
--   $$
--   \pi(Z,X)\le\varepsilon.
--   $$
--
--   In particular the perturbations $Z_\varepsilon$ of the proof of Theorem 1 converge to $X$ as $\varepsilon\downarrow0$ in each of the metrics.
--
--   Differences from the source:
--   - generalization: π^∞_n(Z_ε, X) ⩽ ε, so that Z_ε → X in π^∞_n, the strongest metric considered → every uniform ε-perturbation Z lies in 𝒵 and has π(Z, X) ⩽ ε for each π of Assumption G; reason: Z_ε and π^∞_n are a special case, and the bound for each metric is the content of 'strongest'
--   - generalization: the probability space (Ω, F, P) is atomless (§2.1, p.5) → no atomlessness hypothesis on Ω; reason: it follows from the density of X in Assumption G, so the printed setting is a special case
--   - encoding: π is a real-valued pseudo-metric → π is ℝ≥0∞-valued: levyProkhorovEDist for π^W_n and eLpNorm for π^q_n; reason: same values on the carrier, where the distances are finite
--   - encoding: ℝⁿ with the Euclidean norm, n a positive integer → EuclideanSpace ℝ (Fin n) with 0 < n; reason: same space and norm
-- source:
--   Embrechts–Schied–Wang, Robustness in the Optimization of Risk Measures, arXiv:1809.09268v3, 11 Feb 2021, proof of Theorem 1, p.30

import Mathlib
import Definitions.Def_RobustRiskOpt_Admissible
import Definitions.Def_RobustRiskOpt_Model

open MeasureTheory

namespace RobustRiskOpt

/-- p.30, in the proof of Theorem 1 (Embrechts–Schied–Wang, arXiv:1809.09268v3): a uniform
`ε`-perturbation `Z` of `X` stays in the model and is `ε`-close to `X` in each of the metrics of
Assumption G. The paper records this for `π^∞_n`, "the strongest metric `π` that we consider"; the
statement gives each metric directly. -/
theorem perturbation_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (M : UncertaintyModel) (X Z : Ω → E n)
    (hX : X ∈ M.carrier P) (hZ : Measurable Z) (ε : ℝ) (hε : 0 < ε)
    (hZX : ∀ ω, ‖Z ω - X ω‖ ≤ ε) :
    Z ∈ M.carrier P ∧ M.dist P Z X ≤ ENNReal.ofReal ε := by sorry

end RobustRiskOpt
