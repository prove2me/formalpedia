-- Prove2me | Theorems.Thm_StructBandit_proposition_4
-- name    : StructBandit.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:15.842379+00:00
-- url     : https://prove2.me/theorems/6ade5cdd-0c31-4759-9c3a-377cebc25c68
-- title:
--   Proposition 4 — the deep update $(\eta'_\epsilon(Q),\mu_\epsilon(Q))$ exists and is continuous on $\mathcal P'$
-- statement:
--   Let $\mathcal P$ be a structure set and $\epsilon>0$. The deep update selection rule $(\eta'_\epsilon(Q),\mu_\epsilon(Q))$ of problem (20) exists and is continuous on $\mathcal P'$: there is a map $f$, continuous on $\mathcal P'$, such that for every $Q\in\mathcal P'$, $f(Q)$ is the unique minimizer of (20) at $Q$.
--
--   A continuous selection is what lets the exploration targets computed from estimates converge to the target at the true distribution.
--
--   Differences from the source:
--
--   - reading: Assumption 1(2): Rewmax(x,P) ≠ Rew⋆(P) for any x ∈ X (p.19) → Rewmax(x,P) ≠ Rew⋆(P) for every suboptimal x ∈ X̃(P) (PPrime); reason: as printed it fails at x = x⋆(P) for every P (Q = P is feasible in (8) and fixes the optimal column), so 𝒫′ would be empty and the statement vacuous; the paper's gloss (p.19) and counterexample (p.20) concern suboptimal arms
--   - reading: (20) types µ(x) ∈ K⋆ × ℝ₊ × ℝ and writes λ(r,x)(x′) → α(x) ∈ ℝ₊, β(x) ∈ ℝ, λ(x) ∈ K⋆; λ(r,x)(x′) is the (r,x) entry of λ(x′), for every r ∈ R; reason: the order and roles of (α, β, λ) used everywhere else in the paper (pp.22, 24)
--   - encoding: 'exists and is continuous on 𝒫′' → ∃ f continuous on 𝒫′ with IsDUSol Q ε η µ ↔ (η, µ) = f Q for Q ∈ 𝒫′; reason: existence, uniqueness of the argmin and continuity of the selection in one statement
--   - encoding: I, Dist, C, C̄, Rewmax, Dual, Dual‾ as extended-real optimal values ('max' over ρ ≥ 0 in (17) and 'max' in (8) included); SU := +∞ if (19) is infeasible → EReal values with inf ∅ = +∞, sup ∅ = −∞; SU returns Option (none = +∞), and none also when (19) is feasible but has no minimizer; reason: the source's conventions; a supremum need not be attained off the source's setting; (19) is an argmin, so nothing is defined without a minimizer; Lean's log 0 = 0 and x/0 = 0 decide no case
--   - reading: χ_{−∞}(η(x) − λ(r,x) − β − αr𝟙(x = x′) ≥ 0) in (14), with no index range → the constraint for every x ∈ X̃(P), r ∈ R; a log term is 0 if η(x)P(r,x) = 0 and −∞ if its argument is 0; reason: the range of the sum it closes, and the values the derivation of App. C.2 (p.43) gives at the boundary
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Proposition 4, p.27 (proof App. H.3)

import Mathlib
import Definitions.Def_StructBandit_IsDUSol

open scoped BigOperators

namespace StructBandit

/-- **Proposition 4 (Continuous Selection Rule for the Deep Update Algorithm).**
Van Parys & Golrezaei, arXiv:2007.07302v3, Proposition 4, p.27 (proof App. H.3).

The deep update selection rule `(η′_ε(Q), µ_ε(Q))` of (20) exists and is continuous on `𝒫′`: for every
`ε > 0` there is a map `f`, continuous on `𝒫′`, such that at every `Q ∈ 𝒫′` the pair `f(Q)` is the
(unique) minimizer of (20).

**Formalization Note.** `𝒫′` is `PPrime S` (Assumption 1 with condition 2 read over suboptimal arms). The
codomain `(X → ℝ) × (X → ℝ × ℝ × (R → X → ℝ))` carries the product topology. -/
theorem proposition_4 {X : Type*} [Fintype X] [Nonempty X] {R : Finset ℝ} {S : Set (R → X → ℝ)}
    (hS : IsStructureSet S) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : (R → X → ℝ) → (X → ℝ) × (X → DualVec R X), ContinuousOn f (PPrime S) ∧
      ∀ Q ∈ PPrime S, ∀ (η : X → ℝ) (μs : X → DualVec R X),
        IsDUSol S Q ε η μs ↔ (η, μs) = f Q := by sorry

end StructBandit
