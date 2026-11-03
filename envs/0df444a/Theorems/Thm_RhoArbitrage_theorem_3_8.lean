-- Prove2me | Theorems.Thm_RhoArbitrage_theorem_3_8
-- name    : RhoArbitrage.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:46.09948+00:00
-- url     : https://prove2.me/theorems/5a9490ab-a983-4df5-b33c-46c2eae0add9
-- title:
--   Theorem 3.8, p.8 — $\Pi^\rho_\nu$ is nonempty and compact whenever $\rho_\nu<\infty$
-- statement:
--   Assume that $\rho$ is a risk functional that satisfies the Fatou property on $\mathcal X$ and sensitivity to large expected losses on $\mathcal X$. Then for any $\nu\ge0$ with $\rho_\nu<\infty$, the set
--
--   $$
--   \Pi^\rho_\nu
--   $$
--
--   of $\rho$-optimal portfolios for $\nu$ is nonempty and compact.
--
--   This answers the paper's existence question (Q1). It is applied both to $\rho$ and to $\rho^\infty$.
--
--   Differences from the source:
--   - encoding: a Riesz space L∞ ⊂ L ⊂ L¹ of P-a.s. equivalence classes → `L : Set (Ω → ℝ)`, the set of representatives, with `IsRieszL P L`; reason: the Riesz, L¹ and L∞ conditions are stated on functions and force closure under a.s. equality, so the instances are the same
--   - encoding: ρ : L → (−∞, ∞] → `ρ : (Ω → ℝ) → EReal` with `IsRiskFunctional P L ρ`, which includes `ρ X ≠ ⊥` on L; reason: only the values on L are constrained, and every statement evaluates ρ on L only
--   - reading: nonredundant: Σ_{i=0}^d ϑⁱSⁱ = 0 P-a.s. implies ϑ = 0 (§2.2, p.5) → the combination vanishes at time 0 and P-a.s. at time 1 (`Market.Standing.nonredundant`); reason: Sⁱ is a process, and this is the weaker of the two readings as an assumption (the time-1 reading implies it), so the theorem is the stronger one
--   - encoding: risky assets i ∈ {1, …, d}, portfolios π ∈ ℝ^d → `Fin M.d` and `Fin M.d → ℝ`; reason: indexing only; the riskless asset is determined by r and is not a field of `Market`
--   - encoding: X ∈ 𝒴 \ {0} and λX ∉ 𝒜_ρ (Definition 3.6) → `¬ (X =ᵐ[P] 0)` and `0 < ρ (lam • X)`; reason: elements of L are a.s. classes, so "≠ 0" is a.s.; λX ∈ L, so not being in the acceptance set is ρ(λX) > 0
--   - encoding: sequences indexed by n ≥ 1 → sequences indexed by `n : ℕ`; reason: a shift of the index
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, Theorem 3.8, p.8

import Mathlib
import Definitions.Def_RhoArbitrage_IsRieszL
import Definitions.Def_RhoArbitrage_IsRiskFunctional
import Definitions.Def_RhoArbitrage_HasFatouOn
import Definitions.Def_RhoArbitrage_SensitiveToLargeExpectedLossesOn
import Definitions.Def_RhoArbitrage_Market
import Definitions.Def_RhoArbitrage_Market_rhoNu

open MeasureTheory

namespace RhoArbitrage

/-- **Theorem 3.8 (existence and compactness of `ρ`-optimal portfolios).** Herdegen–Khan,
arXiv:2202.07610v3, Theorem 3.8, p.8.

If `ρ` is a risk functional with the Fatou property on `𝒳` and sensitivity to large expected losses
on `𝒳`, then for any `ν ≥ 0` with `ρ_ν < ∞`, the set `Π^ρ_ν` is nonempty and compact. -/
theorem theorem_3_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (L : Set (Ω → ℝ)) (hL : IsRieszL P L) (ρ : (Ω → ℝ) → EReal)
    (hρ : IsRiskFunctional P L ρ) (M : Market Ω) (hM : M.Standing P L)
    (hF : HasFatouOn P L M.excessSpace ρ)
    (hS : SensitiveToLargeExpectedLossesOn P M.excessSpace ρ) (ν : ℝ) (hν : 0 ≤ ν)
    (hfin : M.rhoNu P ρ ν < ⊤) :
    (M.optSet P ρ ν).Nonempty ∧ IsCompact (M.optSet P ρ ν) := by sorry

end RhoArbitrage
