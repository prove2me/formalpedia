-- Prove2me | Theorems.Thm_RhoArbitrage_proposition_C_1
-- name    : RhoArbitrage.proposition_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:25:49.586493+00:00
-- url     : https://prove2.me/theorems/f2b350ed-75bf-42e5-a026-5343b1dd7a57
-- title:
--   Proposition C.1, p.24 — an unbounded sequence of bounded risk yields a nonzero recession portfolio
-- statement:
--   Let $\rho$ be a risk functional that satisfies the Fatou property on $\mathcal X$ and let $c\ge0$. Assume that $(\pi_n)_{n\ge1}\subset\mathbb R^d$ is an unbounded sequence of portfolios with $\rho(X_{\pi_n})\le c$ for all $n$. Then there is a portfolio $\pi\in\mathbb R^d\setminus\{0\}$ with
--
--   $$
--   \rho(\lambda X_\pi)\le c\quad\text{for all }\lambda>0 .
--   $$
--
--   Moreover, if $\mathbb E[X_{\pi_n}]=0$ for all $n$, then the same $\pi$ can be taken with $\mathbb E[X_\pi]=0$.
--
--   This is the compactness input to the existence of optimal portfolios: risk that stays bounded along an unbounded sequence produces a whole ray of portfolios of bounded risk.
--
--   **Formalization Note** One witness $\pi$ serves both clauses.
--
--   Differences from the source:
--   - encoding: a Riesz space L∞ ⊂ L ⊂ L¹ of P-a.s. equivalence classes → `L : Set (Ω → ℝ)`, the set of representatives, with `IsRieszL P L`; reason: the Riesz, L¹ and L∞ conditions are stated on functions and force closure under a.s. equality, so the instances are the same
--   - encoding: ρ : L → (−∞, ∞] → `ρ : (Ω → ℝ) → EReal` with `IsRiskFunctional P L ρ`, which includes `ρ X ≠ ⊥` on L; reason: only the values on L are constrained, and every statement evaluates ρ on L only
--   - reading: nonredundant: Σ_{i=0}^d ϑⁱSⁱ = 0 P-a.s. implies ϑ = 0 (§2.2, p.5) → the combination vanishes at time 0 and P-a.s. at time 1 (`Market.Standing.nonredundant`); reason: Sⁱ is a process, and this is the weaker of the two readings as an assumption (the time-1 reading implies it), so the theorem is the stronger one
--   - encoding: risky assets i ∈ {1, …, d}, portfolios π ∈ ℝ^d → `Fin M.d` and `Fin M.d → ℝ`; reason: indexing only; the riskless asset is determined by r and is not a field of `Market`
--   - encoding: sequences indexed by n ≥ 1 → sequences indexed by `n : ℕ`; reason: a shift of the index
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, Proposition C.1, p.24

import Mathlib
import Definitions.Def_RhoArbitrage_IsRieszL
import Definitions.Def_RhoArbitrage_IsRiskFunctional
import Definitions.Def_RhoArbitrage_HasFatouOn
import Definitions.Def_RhoArbitrage_Market

open MeasureTheory

namespace RhoArbitrage

/-- **Proposition C.1.** Herdegen–Khan, arXiv:2202.07610v3, Proposition C.1, p.24.

Let `ρ` be a risk functional with the Fatou property on `𝒳` and let `c ≥ 0`. If there is an
unbounded sequence of portfolios `(πₙ) ⊂ ℝ^d` with `ρ(X_{πₙ}) ≤ c` for all `n`, then there is a
portfolio `π ∈ ℝ^d \ {0}` with `ρ(λX_π) ≤ c` for all `λ > 0`; and if `E[X_{πₙ}] = 0` for all `n`,
we may further assume `E[X_π] = 0`.

**Formalization Note.** One witness `π` serves both clauses ("we may further assume"): the
implication sits inside the existential. Boundedness is independent of the norm on `ℝ^d`. -/
theorem proposition_C_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (L : Set (Ω → ℝ)) (hL : IsRieszL P L) (ρ : (Ω → ℝ) → EReal)
    (hρ : IsRiskFunctional P L ρ) (M : Market Ω) (hM : M.Standing P L)
    (hF : HasFatouOn P L M.excessSpace ρ) (c : ℝ) (hc : 0 ≤ c) (πs : ℕ → Fin M.d → ℝ)
    (hunb : ¬ Bornology.IsBounded (Set.range πs)) (hle : ∀ n, ρ (M.X (πs n)) ≤ (c : EReal)) :
    ∃ π : Fin M.d → ℝ, π ≠ 0 ∧ (∀ lam : ℝ, 0 < lam → ρ (lam • M.X π) ≤ (c : EReal)) ∧
      ((∀ n, ∫ ω, M.X (πs n) ω ∂P = 0) → ∫ ω, M.X π ω ∂P = 0) := by sorry

end RhoArbitrage
