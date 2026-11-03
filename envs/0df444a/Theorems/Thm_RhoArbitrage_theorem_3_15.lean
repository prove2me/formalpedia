-- Prove2me | Theorems.Thm_RhoArbitrage_theorem_3_15
-- name    : RhoArbitrage.theorem_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:41.586687+00:00
-- url     : https://prove2.me/theorems/ceecdced-7df3-4ba4-8544-58cf170b6b75
-- title:
--   Theorem 3.15, pp.9–10 — no $\rho$-arbitrage $\iff$ no $\rho^\infty$-arbitrage $\iff$ $\rho^\infty_1>0$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $L$ a Riesz space with $L^\infty\subset L\subset L^1$, and $(S^0,S)$ a one-period market satisfying the standing assumptions of Section 2.2. Assume that $\rho$ is a risk functional that satisfies the Fatou property on $\mathcal X$ and sensitivity to large expected losses on $\mathcal X$. Then the following are equivalent:
--
--   1. $\rho^\infty_1>0$;
--   2. the market $(S^0,S)$ does not admit $\rho^\infty$-arbitrage;
--   3. the market $(S^0,S)$ does not admit $\rho$-arbitrage.
--
--   So for a star-shaped $\rho$, which need not be convex, cash-invariant or positively homogeneous, the question of $\rho$-arbitrage reduces to the positively homogeneous functional $\rho^\infty$ and is decided by the sign of the single number $\rho^\infty_1$. The value $\rho^\infty_1=+\infty$ falls under the first statement.
--
--   Differences from the source:
--   - encoding: a Riesz space L∞ ⊂ L ⊂ L¹ of P-a.s. equivalence classes → `L : Set (Ω → ℝ)`, the set of representatives, with `IsRieszL P L`; reason: the Riesz, L¹ and L∞ conditions are stated on functions and force closure under a.s. equality, so the instances are the same
--   - encoding: ρ : L → (−∞, ∞] → `ρ : (Ω → ℝ) → EReal` with `IsRiskFunctional P L ρ`, which includes `ρ X ≠ ⊥` on L; reason: only the values on L are constrained, and every statement evaluates ρ on L only
--   - encoding: ρ∞(X) := lim_{t→∞} ρ(tX)/t (display (2.1)) → `rhoInf ρ X := ⨆ t ≥ 1, t⁻¹ * ρ (t • X)`; reason: for a star-shaped ρ the quotient is nondecreasing in t, so the supremum is the limit; `RhoArbitrage.display_2_1` states this
--   - reading: nonredundant: Σ_{i=0}^d ϑⁱSⁱ = 0 P-a.s. implies ϑ = 0 (§2.2, p.5) → the combination vanishes at time 0 and P-a.s. at time 1 (`Market.Standing.nonredundant`); reason: Sⁱ is a process, and this is the weaker of the two readings as an assumption (the time-1 reading implies it), so the theorem is the stronger one
--   - encoding: risky assets i ∈ {1, …, d}, portfolios π ∈ ℝ^d → `Fin M.d` and `Fin M.d → ℝ`; reason: indexing only; the riskless asset is determined by r and is not a field of `Market`
--   - encoding: X ∈ 𝒴 \ {0} and λX ∉ 𝒜_ρ (Definition 3.6) → `¬ (X =ᵐ[P] 0)` and `0 < ρ (lam • X)`; reason: elements of L are a.s. classes, so "≠ 0" is a.s.; λX ∈ L, so not being in the acceptance set is ρ(λX) > 0
--   - encoding: sequences indexed by n ≥ 1 → sequences indexed by `n : ℕ`; reason: a shift of the index
--   - reading: E[X_{πₙ}] ↑ ∞ (Definition 3.3) → `Monotone` and `Tendsto … atTop atTop`; reason: nondecreasing and tending to +∞; the strictly increasing reading gives the same notion because such a sequence has a strictly increasing subsequence
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, Theorem 3.15, pp.9–10

import Mathlib
import Definitions.Def_RhoArbitrage_IsRieszL
import Definitions.Def_RhoArbitrage_IsRiskFunctional
import Definitions.Def_RhoArbitrage_HasFatouOn
import Definitions.Def_RhoArbitrage_SensitiveToLargeExpectedLossesOn
import Definitions.Def_RhoArbitrage_rhoInf
import Definitions.Def_RhoArbitrage_Market
import Definitions.Def_RhoArbitrage_Market_rhoNu
import Definitions.Def_RhoArbitrage_Market_AdmitsArbitrage

open MeasureTheory

namespace RhoArbitrage

/-- **Theorem 3.15 (primal characterisation of `ρ`-arbitrage).** Herdegen–Khan,
arXiv:2202.07610v3, Theorem 3.15, pp.9–10.

Assume `ρ` is a risk functional that satisfies the Fatou property on `𝒳` and sensitivity to large
expected losses on `𝒳`. Then the following are equivalent:

* (a) `ρ∞_1 > 0`;
* (b) the market `(S⁰, S)` does not admit `ρ∞`-arbitrage;
* (c) the market `(S⁰, S)` does not admit `ρ`-arbitrage.

**Formalization Note.** The hypotheses `hL`, `hρ`, `hM` are the standing assumptions of §2.1–§2.2,
which the theorem's sentence does not repeat. `ρ∞_1 > 0` includes `ρ∞_1 = +∞`. -/
theorem theorem_3_15 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (L : Set (Ω → ℝ)) (hL : IsRieszL P L) (ρ : (Ω → ℝ) → EReal)
    (hρ : IsRiskFunctional P L ρ) (M : Market Ω) (hM : M.Standing P L)
    (hF : HasFatouOn P L M.excessSpace ρ)
    (hS : SensitiveToLargeExpectedLossesOn P M.excessSpace ρ) :
    List.TFAE [0 < M.rhoNu P (rhoInf ρ) 1, ¬ M.AdmitsArbitrage P (rhoInf ρ),
      ¬ M.AdmitsArbitrage P ρ] := by sorry

end RhoArbitrage
