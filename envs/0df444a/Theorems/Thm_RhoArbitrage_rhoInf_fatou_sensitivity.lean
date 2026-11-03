-- Prove2me | Theorems.Thm_RhoArbitrage_rhoInf_fatou_sensitivity
-- name    : RhoArbitrage.rhoInf_fatou_sensitivity
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:25:39.834612+00:00
-- url     : https://prove2.me/theorems/2951de71-882a-41f1-9335-e4fcf0515fb3
-- title:
--   Proof of Theorem 3.15, p.27 — the Fatou property and sensitivity pass from $\rho$ to $\rho^\infty$ on $\mathcal X$
-- statement:
--   Let $\rho$ be a risk functional that satisfies the Fatou property on $\mathcal X$ and sensitivity to large expected losses on $\mathcal X$. Then $\rho^\infty$ also satisfies the Fatou property on $\mathcal X$ and sensitivity to large expected losses on $\mathcal X$.
--
--   This lets the existence theorem be applied to $\rho^\infty$ as well as to $\rho$.
--
--   **Formalization Note** The statement is for $\mathcal X$, a linear subspace, as in the paper's proof. The more general sentence on p.5 about the Fatou property on an arbitrary $\mathcal Y\subset L$ is not posed: it fails for a $\mathcal Y$ not closed under positive scaling, and it is not used.
--
--   Differences from the source:
--   - encoding: a Riesz space L∞ ⊂ L ⊂ L¹ of P-a.s. equivalence classes → `L : Set (Ω → ℝ)`, the set of representatives, with `IsRieszL P L`; reason: the Riesz, L¹ and L∞ conditions are stated on functions and force closure under a.s. equality, so the instances are the same
--   - encoding: ρ : L → (−∞, ∞] → `ρ : (Ω → ℝ) → EReal` with `IsRiskFunctional P L ρ`, which includes `ρ X ≠ ⊥` on L; reason: only the values on L are constrained, and every statement evaluates ρ on L only
--   - encoding: ρ∞(X) := lim_{t→∞} ρ(tX)/t (display (2.1)) → `rhoInf ρ X := ⨆ t ≥ 1, t⁻¹ * ρ (t • X)`; reason: for a star-shaped ρ the quotient is nondecreasing in t, so the supremum is the limit; `RhoArbitrage.display_2_1` states this
--   - reading: nonredundant: Σ_{i=0}^d ϑⁱSⁱ = 0 P-a.s. implies ϑ = 0 (§2.2, p.5) → the combination vanishes at time 0 and P-a.s. at time 1 (`Market.Standing.nonredundant`); reason: Sⁱ is a process, and this is the weaker of the two readings as an assumption (the time-1 reading implies it), so the theorem is the stronger one
--   - encoding: risky assets i ∈ {1, …, d}, portfolios π ∈ ℝ^d → `Fin M.d` and `Fin M.d → ℝ`; reason: indexing only; the riskless asset is determined by r and is not a field of `Market`
--   - encoding: X ∈ 𝒴 \ {0} and λX ∉ 𝒜_ρ (Definition 3.6) → `¬ (X =ᵐ[P] 0)` and `0 < ρ (lam • X)`; reason: elements of L are a.s. classes, so "≠ 0" is a.s.; λX ∈ L, so not being in the acceptance set is ρ(λX) > 0
--   - encoding: sequences indexed by n ≥ 1 → sequences indexed by `n : ℕ`; reason: a shift of the index
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, proof of Theorem 3.15, p.27

import Mathlib
import Definitions.Def_RhoArbitrage_IsRieszL
import Definitions.Def_RhoArbitrage_IsRiskFunctional
import Definitions.Def_RhoArbitrage_HasFatouOn
import Definitions.Def_RhoArbitrage_SensitiveToLargeExpectedLossesOn
import Definitions.Def_RhoArbitrage_rhoInf
import Definitions.Def_RhoArbitrage_Market

open MeasureTheory

namespace RhoArbitrage

/-- **The Fatou property and sensitivity to large expected losses pass from `ρ` to `ρ∞` on `𝒳`.**
Herdegen–Khan, arXiv:2202.07610v3, proof of Theorem 3.15, p.27: "Since `ρ` satisfies the Fatou
property on `𝒳` and sensitivity to large expected losses on `𝒳`, so too does `ρ∞`."

**Formalization Note.** The statement is for `𝒳`, as in the proof on p.27. The sentence on p.5
that the Fatou property on *some* `𝒴 ⊂ L` passes to `ρ∞` is not posed: it fails for a `𝒴` that is
not closed under positive scaling, and the proof on p.27 needs only `𝒳`. -/
theorem rhoInf_fatou_sensitivity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (L : Set (Ω → ℝ)) (hL : IsRieszL P L) (ρ : (Ω → ℝ) → EReal)
    (hρ : IsRiskFunctional P L ρ) (M : Market Ω) (hM : M.Standing P L)
    (hF : HasFatouOn P L M.excessSpace ρ)
    (hS : SensitiveToLargeExpectedLossesOn P M.excessSpace ρ) :
    HasFatouOn P L M.excessSpace (rhoInf ρ) ∧
      SensitiveToLargeExpectedLossesOn P M.excessSpace (rhoInf ρ) := by sorry

end RhoArbitrage
