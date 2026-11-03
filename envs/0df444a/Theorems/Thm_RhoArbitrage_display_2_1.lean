-- Prove2me | Theorems.Thm_RhoArbitrage_display_2_1
-- name    : RhoArbitrage.display_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:25:32.753904+00:00
-- url     : https://prove2.me/theorems/e0e8cec8-170b-4820-8e21-73d467451dde
-- title:
--   Display (2.1), p.5 — $\rho^\infty$ is the limit of $\rho(tX)/t$, a risk functional and the smallest positively homogeneous majorant of $\rho$
-- statement:
--   Let $\rho$ be a risk functional on the Riesz space $L$. Then:
--
--   1. for every $X\in L$, the limit exists in $(-\infty,\infty]$ and
--
--   $$
--   \lim_{t\to\infty}\frac{\rho(tX)}{t}=\rho^\infty(X);
--   $$
--
--   2. $\rho^\infty$ is a risk functional on $L$;
--   3. $\rho^\infty(\lambda X)=\lambda\rho^\infty(X)$ for all $X\in L$ and $\lambda>0$;
--   4. $\rho\le\rho^\infty$ on $L$;
--   5. $\rho^\infty\le\eta$ on $L$ for every positively homogeneous $\eta$ with $\rho\le\eta$ on $L$.
--
--   This reduces the large-scale behaviour of a star-shaped risk functional to a positively homogeneous one, and it justifies the definition of $\rho^\infty$ used throughout the mission.
--
--   Differences from the source:
--   - encoding: a Riesz space L∞ ⊂ L ⊂ L¹ of P-a.s. equivalence classes → `L : Set (Ω → ℝ)`, the set of representatives, with `IsRieszL P L`; reason: the Riesz, L¹ and L∞ conditions are stated on functions and force closure under a.s. equality, so the instances are the same
--   - encoding: ρ : L → (−∞, ∞] → `ρ : (Ω → ℝ) → EReal` with `IsRiskFunctional P L ρ`, which includes `ρ X ≠ ⊥` on L; reason: only the values on L are constrained, and every statement evaluates ρ on L only
--   - encoding: ρ∞(X) := lim_{t→∞} ρ(tX)/t (display (2.1)) → `rhoInf ρ X := ⨆ t ≥ 1, t⁻¹ * ρ (t • X)`; reason: for a star-shaped ρ the quotient is nondecreasing in t, so the supremum is the limit; `RhoArbitrage.display_2_1` states this
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, §2.1, p.5, display (2.1)

import Mathlib
import Definitions.Def_RhoArbitrage_IsRieszL
import Definitions.Def_RhoArbitrage_IsRiskFunctional
import Definitions.Def_RhoArbitrage_rhoInf

open MeasureTheory Filter Topology

namespace RhoArbitrage

/-- **`ρ∞` is the smallest positively homogeneous majorant of `ρ`, and a risk functional.**
Herdegen–Khan, arXiv:2202.07610v3, §2.1, p.5, display (2.1).

For a risk functional `ρ` on `L`: (i) `ρ(tX)/t → ρ∞(X)` as `t → ∞`, for every `X ∈ L`; (ii) `ρ∞`
is a risk functional on `L`; (iii) `ρ∞` is positively homogeneous on `L`; (iv) `ρ ≤ ρ∞` on `L`;
(v) `ρ∞ ≤ η` on `L` for every positively homogeneous `η` with `ρ ≤ η` on `L`.

**Formalization Note.** The limit in (i) is along real `t → ∞` in `EReal`. Clause (v) quantifies
over all positively homogeneous majorants, not only risk functionals. -/
theorem display_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Set (Ω → ℝ)) (hL : IsRieszL P L) (ρ : (Ω → ℝ) → EReal) (hρ : IsRiskFunctional P L ρ) :
    (∀ X ∈ L, Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * ρ (t • X)) atTop (𝓝 (rhoInf ρ X))) ∧
    IsRiskFunctional P L (rhoInf ρ) ∧
    (∀ X ∈ L, ∀ lam : ℝ, 0 < lam → rhoInf ρ (lam • X) = (lam : EReal) * rhoInf ρ X) ∧
    (∀ X ∈ L, ρ X ≤ rhoInf ρ X) ∧
    (∀ η : (Ω → ℝ) → EReal,
      (∀ X ∈ L, ∀ lam : ℝ, 0 < lam → η (lam • X) = (lam : EReal) * η X) →
      (∀ X ∈ L, ρ X ≤ η X) → ∀ X ∈ L, rhoInf ρ X ≤ η X) := by sorry

end RhoArbitrage
