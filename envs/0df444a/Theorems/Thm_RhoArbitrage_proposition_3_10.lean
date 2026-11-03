-- Prove2me | Theorems.Thm_RhoArbitrage_proposition_3_10
-- name    : RhoArbitrage.proposition_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:30.995893+00:00
-- url     : https://prove2.me/theorems/486a84e4-1e8e-4311-a436-4205d45c1aac
-- title:
--   Proposition 3.10, p.8 — $\rho^\infty_\nu$ is the smallest positively homogeneous majorant of $\rho_\nu$ and $\rho^\infty_1>0\iff\nu^+<\infty$
-- statement:
--   Let $\rho$ be a risk functional that satisfies the Fatou property on $\mathcal X$ and sensitivity to large expected losses on $\mathcal X$. Then $\nu\mapsto\rho_\nu$ is $(-\infty,\infty]$-valued and lower semi-continuous on $\mathbb R_+$. Its smallest positively homogeneous majorant is $\nu\mapsto\rho^\infty_\nu$, and
--
--   $$
--   \rho^\infty_1>0\iff\nu^+<\infty .
--   $$
--
--   Moreover:
--
--   1. if $\rho^\infty_1>0$, then $\nu_{\min}<\infty$ and $\rho_{\min}=\rho_{\nu_{\min}}\in(-\infty,0]$;
--   2. if $\rho^\infty_1=0$, then $\nu_{\min}\in[0,\infty]$ and $\rho_{\min}\in[-\infty,0]$;
--   3. if $\rho^\infty_1<0$, then $\nu_{\min}=\infty$ and $\rho_{\min}=-\infty$.
--
--   This describes the shape of the optimal boundary, and the equivalence is the step from $\rho^\infty_1>0$ to the absence of $\rho$-arbitrage.
--
--   **Formalization Note** In case 1, $\nu_{\min}$ is finite and $\rho_{\nu_{\min}}$ is evaluated at its real value. In case 2, $\nu_{\min}\in[0,\infty]$ holds by the type of $\nu_{\min}$, and $\rho_{\min}\in[-\infty,0]$ is $\rho_{\min}\le0$.
--
--   Differences from the source:
--   - encoding: a Riesz space L∞ ⊂ L ⊂ L¹ of P-a.s. equivalence classes → `L : Set (Ω → ℝ)`, the set of representatives, with `IsRieszL P L`; reason: the Riesz, L¹ and L∞ conditions are stated on functions and force closure under a.s. equality, so the instances are the same
--   - encoding: ρ : L → (−∞, ∞] → `ρ : (Ω → ℝ) → EReal` with `IsRiskFunctional P L ρ`, which includes `ρ X ≠ ⊥` on L; reason: only the values on L are constrained, and every statement evaluates ρ on L only
--   - encoding: ρ∞(X) := lim_{t→∞} ρ(tX)/t (display (2.1)) → `rhoInf ρ X := ⨆ t ≥ 1, t⁻¹ * ρ (t • X)`; reason: for a star-shaped ρ the quotient is nondecreasing in t, so the supremum is the limit; `RhoArbitrage.display_2_1` states this
--   - reading: nonredundant: Σ_{i=0}^d ϑⁱSⁱ = 0 P-a.s. implies ϑ = 0 (§2.2, p.5) → the combination vanishes at time 0 and P-a.s. at time 1 (`Market.Standing.nonredundant`); reason: Sⁱ is a process, and this is the weaker of the two readings as an assumption (the time-1 reading implies it), so the theorem is the stronger one
--   - encoding: risky assets i ∈ {1, …, d}, portfolios π ∈ ℝ^d → `Fin M.d` and `Fin M.d → ℝ`; reason: indexing only; the riskless asset is determined by r and is not a field of `Market`
--   - encoding: X ∈ 𝒴 \ {0} and λX ∉ 𝒜_ρ (Definition 3.6) → `¬ (X =ᵐ[P] 0)` and `0 < ρ (lam • X)`; reason: elements of L are a.s. classes, so "≠ 0" is a.s.; λX ∈ L, so not being in the acceptance set is ρ(λX) > 0
--   - encoding: sequences indexed by n ≥ 1 → sequences indexed by `n : ℕ`; reason: a shift of the index
--   - encoding: maps ν ↦ ρ_ν from ℝ₊ to [−∞, ∞] → maps `ℝ → EReal` with all clauses restricted to `0 ≤ ν`; reason: values at negative ν do not occur in any clause
--   - encoding: ν⁺, ν_min ∈ [0, ∞] → values in `ℝ≥0∞`, built with `ENNReal.ofReal`, and `(M.nuMin P ρ).toReal` in `ρ_{ν_min}`; reason: the same numbers with inf ∅ = ∞; the conversion is applied only where ν_min < ∞
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, Proposition 3.10, p.8

import Mathlib
import Definitions.Def_RhoArbitrage_IsRieszL
import Definitions.Def_RhoArbitrage_IsRiskFunctional
import Definitions.Def_RhoArbitrage_HasFatouOn
import Definitions.Def_RhoArbitrage_SensitiveToLargeExpectedLossesOn
import Definitions.Def_RhoArbitrage_rhoInf
import Definitions.Def_RhoArbitrage_Market
import Definitions.Def_RhoArbitrage_Market_rhoNu
import Definitions.Def_RhoArbitrage_Market_nuPlus
import Definitions.Def_RhoArbitrage_IsSmallestPosHomMajorant

open MeasureTheory

namespace RhoArbitrage

/-- **Proposition 3.10.** Herdegen–Khan, arXiv:2202.07610v3, Proposition 3.10, p.8.

Let `ρ` be a risk functional with the Fatou property on `𝒳` and sensitivity to large expected
losses on `𝒳`. Then `ν ↦ ρ_ν` is `(-∞, ∞]`-valued and lower semi-continuous on `ℝ₊`. Its smallest
positively homogeneous majorant is `ν ↦ ρ∞_ν`, and `ρ∞_1 > 0` if and only if `ν⁺ < ∞`. Moreover:

* (a) if `ρ∞_1 > 0`, then `ν_min < ∞` and `ρ_min = ρ_{ν_min} ∈ (-∞, 0]`;
* (b) if `ρ∞_1 = 0`, then `ν_min ∈ [0, ∞]` and `ρ_min ∈ [-∞, 0]`;
* (c) if `ρ∞_1 < 0`, then `ν_min = ∞` and `ρ_min = -∞`.

**Formalization Note.** Lower semi-continuity is `LowerSemicontinuousOn _ (Set.Ici 0)`, relative
to `ℝ₊`. In (a), `ν_min` is finite, so `ρ_{ν_min}` is evaluated at `(M.nuMin P ρ).toReal`. In (b),
`ν_min ∈ [0, ∞]` is automatic for a value in `ℝ≥0∞` and `ρ_min ∈ [-∞, 0]` is `ρ_min ≤ 0`. -/
theorem proposition_3_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (L : Set (Ω → ℝ)) (hL : IsRieszL P L) (ρ : (Ω → ℝ) → EReal)
    (hρ : IsRiskFunctional P L ρ) (M : Market Ω) (hM : M.Standing P L)
    (hF : HasFatouOn P L M.excessSpace ρ)
    (hS : SensitiveToLargeExpectedLossesOn P M.excessSpace ρ) :
    (∀ ν : ℝ, 0 ≤ ν → M.rhoNu P ρ ν ≠ ⊥) ∧
    LowerSemicontinuousOn (M.rhoNu P ρ) (Set.Ici 0) ∧
    IsSmallestPosHomMajorant (M.rhoNu P ρ) (M.rhoNu P (rhoInf ρ)) ∧
    (0 < M.rhoNu P (rhoInf ρ) 1 ↔ M.nuPlus P ρ < ⊤) ∧
    (0 < M.rhoNu P (rhoInf ρ) 1 →
      M.nuMin P ρ < ⊤ ∧ M.rhoMin P ρ = M.rhoNu P ρ (M.nuMin P ρ).toReal ∧
        M.rhoMin P ρ ≠ ⊥ ∧ M.rhoMin P ρ ≤ 0) ∧
    (M.rhoNu P (rhoInf ρ) 1 = 0 → M.rhoMin P ρ ≤ 0) ∧
    (M.rhoNu P (rhoInf ρ) 1 < 0 → M.nuMin P ρ = ⊤ ∧ M.rhoMin P ρ = ⊥) := by sorry

end RhoArbitrage
