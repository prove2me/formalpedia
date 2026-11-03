-- Prove2me | Theorems.Thm_RhoArbitrage_proposition_3_9
-- name    : RhoArbitrage.proposition_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:38.456398+00:00
-- url     : https://prove2.me/theorems/7a8788c6-b362-41bd-aa10-62f64535eb0a
-- title:
--   Proposition 3.9, p.8 — $\nu\mapsto\rho_\nu$ is star-shaped and $\nu\mapsto\rho^\infty_\nu$ is a positively homogeneous majorant
-- statement:
--   For a risk functional $\rho$, the map $\nu\mapsto\rho_\nu$ from $\mathbb R_+$ to $[-\infty,\infty]$ is star-shaped, that is, for all $\nu\in\mathbb R_+$ and $\lambda\in[1,\infty)$,
--
--   $$
--   \rho_{\lambda\nu}\ge\lambda\rho_\nu .
--   $$
--
--   Moreover, $\rho_0\le0$, and the map $\nu\mapsto\rho^\infty_\nu$ from $\mathbb R_+$ to $[-\infty,\infty]$ is a positively homogeneous majorant of $\nu\mapsto\rho_\nu$.
--
--   So the $\rho$-optimal boundary lies to the left of the $\rho^\infty$-optimal boundary in the mean-risk plane. No Fatou or sensitivity assumption is needed.
--
--   Differences from the source:
--   - encoding: a Riesz space L∞ ⊂ L ⊂ L¹ of P-a.s. equivalence classes → `L : Set (Ω → ℝ)`, the set of representatives, with `IsRieszL P L`; reason: the Riesz, L¹ and L∞ conditions are stated on functions and force closure under a.s. equality, so the instances are the same
--   - encoding: ρ : L → (−∞, ∞] → `ρ : (Ω → ℝ) → EReal` with `IsRiskFunctional P L ρ`, which includes `ρ X ≠ ⊥` on L; reason: only the values on L are constrained, and every statement evaluates ρ on L only
--   - encoding: ρ∞(X) := lim_{t→∞} ρ(tX)/t (display (2.1)) → `rhoInf ρ X := ⨆ t ≥ 1, t⁻¹ * ρ (t • X)`; reason: for a star-shaped ρ the quotient is nondecreasing in t, so the supremum is the limit; `RhoArbitrage.display_2_1` states this
--   - reading: nonredundant: Σ_{i=0}^d ϑⁱSⁱ = 0 P-a.s. implies ϑ = 0 (§2.2, p.5) → the combination vanishes at time 0 and P-a.s. at time 1 (`Market.Standing.nonredundant`); reason: Sⁱ is a process, and this is the weaker of the two readings as an assumption (the time-1 reading implies it), so the theorem is the stronger one
--   - encoding: risky assets i ∈ {1, …, d}, portfolios π ∈ ℝ^d → `Fin M.d` and `Fin M.d → ℝ`; reason: indexing only; the riskless asset is determined by r and is not a field of `Market`
--   - encoding: maps ν ↦ ρ_ν from ℝ₊ to [−∞, ∞] → maps `ℝ → EReal` with all clauses restricted to `0 ≤ ν`; reason: values at negative ν do not occur in any clause
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, Proposition 3.9, p.8

import Mathlib
import Definitions.Def_RhoArbitrage_IsRieszL
import Definitions.Def_RhoArbitrage_IsRiskFunctional
import Definitions.Def_RhoArbitrage_rhoInf
import Definitions.Def_RhoArbitrage_Market
import Definitions.Def_RhoArbitrage_Market_rhoNu
import Definitions.Def_RhoArbitrage_IsSmallestPosHomMajorant

open MeasureTheory

namespace RhoArbitrage

/-- **Proposition 3.9.** Herdegen–Khan, arXiv:2202.07610v3, Proposition 3.9, p.8.

For a risk functional `ρ`, the map `ν ↦ ρ_ν` from `ℝ₊` to `[-∞, ∞]` is star-shaped: for all
`ν ∈ ℝ₊` and `λ ∈ [1, ∞)`, `ρ_{λν} ≥ λρ_ν`. Moreover `ρ_0 ≤ 0`, and the map `ν ↦ ρ∞_ν` from `ℝ₊` to
`[-∞, ∞]` is a positively homogeneous majorant of `ν ↦ ρ_ν`. -/
theorem proposition_3_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (L : Set (Ω → ℝ)) (hL : IsRieszL P L) (ρ : (Ω → ℝ) → EReal)
    (hρ : IsRiskFunctional P L ρ) (M : Market Ω) (hM : M.Standing P L) :
    (∀ ν : ℝ, 0 ≤ ν → ∀ lam : ℝ, 1 ≤ lam →
      (lam : EReal) * M.rhoNu P ρ ν ≤ M.rhoNu P ρ (lam * ν)) ∧
    M.rhoNu P ρ 0 ≤ 0 ∧
    IsPosHomMajorant (M.rhoNu P ρ) (M.rhoNu P (rhoInf ρ)) := by sorry

end RhoArbitrage
