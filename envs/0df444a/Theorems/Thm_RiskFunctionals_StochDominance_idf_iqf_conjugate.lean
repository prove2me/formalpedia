-- Prove2me | Theorems.Thm_RiskFunctionals_StochDominance_idf_iqf_conjugate
-- name    : RiskFunctionals.StochDominance.idf_iqf_conjugate
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:22.169306+00:00
-- url     : https://prove2.me/theorems/17a673a2-11cc-40ac-aceb-26bf4e908d5b
-- title:
--   Eqs. (1.19)–(1.20) — the IDF and the IQF are mutually dual
-- statement:
--   Let $G$ be a distribution function on $\mathbb R$ whose first moment exists, with integrated distribution function $\mathcal G(u) = \int_{-\infty}^u G(v)\,dv$ and integrated quantile function $\mathcal G^{[-1]}(q) = \int_0^q G^{-1}(r)\,dr$. Then $\mathcal G$ and $\mathcal G^{[-1]}$ are mutually dual in the following sense:
--   $$\mathcal G(u) = \sup\{uq - \mathcal G^{[-1]}(q) : q \in (0,1)\} \quad\text{for every } u \in \mathbb R, \tag{1.19}$$
--   $$\mathcal G^{[-1]}(q) = \sup\{uq - \mathcal G(u) : u \in \mathbb R\} \quad\text{for every } q \in (0,1). \tag{1.20}$$
--
--   This conjugacy is what turns the comparison of IDFs into a comparison of IQFs, the step from part (v) to part (vi) of Theorem 1.13.
--
--   **Formalization Note** Each supremum is stated as a least upper bound (`IsLUB`): the set of values is bounded above and the stated quantity is its least upper bound, so no junk value of a real `sSup` can make the statement vacuous. The book writes (1.20) without a range for $q$; it is formalized for $q \in (0,1)$, the range of (1.18) and (1.19).
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 15, Eqs. (1.19)–(1.20)

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_IntegratedFunctions

namespace RiskFunctionals.StochDominance

open MeasureTheory

/-- Equations (1.19)–(1.20) (Pflug & Römisch, p. 15): for a distribution `G` with a first
moment, the IDF and the IQF are mutually dual,
`𝒢(u) = sup {uq − 𝒢^{[-1]}(q) : q ∈ (0,1)}` for every `u ∈ ℝ`, and
`𝒢^{[-1]}(q) = sup {uq − 𝒢(u) : u ∈ ℝ}` for every `q ∈ (0,1)`.
Each supremum is stated as a least upper bound (`IsLUB`), so the set is bounded above and the
value is the book's. -/
theorem idf_iqf_conjugate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun v : ℝ => v) μ) :
    (∀ u : ℝ, IsLUB {x : ℝ | ∃ q ∈ Set.Ioo (0 : ℝ) 1,
        x = u * q - integratedQuantileFunction μ q} (integratedDistributionFunction μ u)) ∧
    (∀ q ∈ Set.Ioo (0 : ℝ) 1, IsLUB {x : ℝ | ∃ u : ℝ,
        x = u * q - integratedDistributionFunction μ u} (integratedQuantileFunction μ q)) := by sorry

end RiskFunctionals.StochDominance
