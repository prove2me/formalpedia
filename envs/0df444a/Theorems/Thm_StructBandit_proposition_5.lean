-- Prove2me | Theorems.Thm_StructBandit_proposition_5
-- name    : StructBandit.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:36.050646+00:00
-- url     : https://prove2.me/theorems/95dfc134-1c6e-4cc7-a6eb-618599ccfb70
-- title:
--   Proposition 5 — stability of the shallow update at $\mathcal P'$
-- statement:
--   Let $\mathcal P$ be a structure set, $\epsilon>0$ and $P\in\mathcal P'$. Then
--
--   $$
--   \lim_{\kappa\to0}\ \max_{\substack{Q_1,Q_2\in\mathcal P_\Omega\\ \|Q_1-P\|_\infty\le\kappa,\ \|Q_2-P\|_\infty\le\kappa}}\big\|\mathsf{SU}(Q_1,\eta'_\epsilon(Q_2);\mu_\epsilon(Q_2),\epsilon)-\eta'_\epsilon(P)\big\|_2=0 .
--   $$
--
--   That is, the deep update at $P$ exists, and for every $\delta>0$ there is $\kappa>0$ such that for all $Q_1,Q_2$ within $\kappa$ of $P$ the deep update at $Q_2$ exists, the shallow update at $Q_1$ is finite, and its distance to $\eta'_\epsilon(P)$ is at most $\delta$. This is what makes DUSA's exploration rates converge to the desired rate.
--
--   Differences from the source:
--
--   - reading: Assumption 1(2): Rewmax(x,P) ≠ Rew⋆(P) for any x ∈ X (p.19) → Rewmax(x,P) ≠ Rew⋆(P) for every suboptimal x ∈ X̃(P) (PPrime); reason: as printed it fails at x = x⋆(P) for every P (Q = P is feasible in (8) and fixes the optimal column), so 𝒫′ would be empty and the statement vacuous; the paper's gloss (p.19) and counterexample (p.20) concern suboptimal arms
--   - reading: lim_{κ→0} max_{Q₁,Q₂} ‖SU(Q₁, η′_ε(Q₂); µ_ε(Q₂), ε) − η′_ε(P)‖₂ = 0 → (η′_ε(P), µ_ε(P)) exists, and ∀ δ > 0 ∃ κ > 0 ∀ Q₁, Q₂ ∈ P_Ω within κ: the DU pair at Q₂ exists, SU(Q₁, …) = some η₁ and ‖η₁ − η′_ε(P)‖₂ ≤ δ; reason: the reading under which the max is defined and finite; the empirical distributions to which it is applied lie in P_Ω
--   - encoding: I, Dist, C, C̄, Rewmax, Dual, Dual‾ as extended-real optimal values ('max' over ρ ≥ 0 in (17) and 'max' in (8) included); SU := +∞ if (19) is infeasible → EReal values with inf ∅ = +∞, sup ∅ = −∞; SU returns Option (none = +∞), and none also when (19) is feasible but has no minimizer; reason: the source's conventions; a supremum need not be attained off the source's setting; (19) is an argmin, so nothing is defined without a minimizer; Lean's log 0 = 0 and x/0 = 0 decide no case
--   - reading: (20) types µ(x) ∈ K⋆ × ℝ₊ × ℝ and writes λ(r,x)(x′) → α(x) ∈ ℝ₊, β(x) ∈ ℝ, λ(x) ∈ K⋆; λ(r,x)(x′) is the (r,x) entry of λ(x′), for every r ∈ R; reason: the order and roles of (α, β, λ) used everywhere else in the paper (pp.22, 24)
--   - reading: χ_{−∞}(η(x) − λ(r,x) − β − αr𝟙(x = x′) ≥ 0) in (14), with no index range → the constraint for every x ∈ X̃(P), r ∈ R; a log term is 0 if η(x)P(r,x) = 0 and −∞ if its argument is 0; reason: the range of the sum it closes, and the values the derivation of App. C.2 (p.43) gives at the boundary
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Proposition 5, p.28 (proof App. H.4)

import Mathlib
import Definitions.Def_StructBandit_IsDUSol
import Definitions.Def_StructBandit_shallowUpdate

open scoped BigOperators

namespace StructBandit

/-- **Proposition 5 (Stability of the Shallow Update Selection Rule).**
Van Parys & Golrezaei, arXiv:2007.07302v3, Proposition 5, p.28 (proof App. H.4).

For any `P ∈ 𝒫′`,
`lim_{κ→0} max_{Q₁,Q₂ : ‖Q₁−P‖_∞ ≤ κ, ‖Q₂−P‖_∞ ≤ κ} ‖SU(Q₁, η′_ε(Q₂); µ_ε(Q₂), ε) − η′_ε(P)‖₂ = 0`.

**Formalization Note.** `Q₁, Q₂` range over `P_Ω` (DUSA applies the updates at empirical distributions).
The limit is stated in ε–δ form: the deep-update pair `(η′_ε(P), µ_ε(P))` exists, and for every `δ > 0`
there is `κ > 0` such that for all `Q₁, Q₂ ∈ P_Ω` within `κ` of `P` in `‖·‖_∞`, the deep update at `Q₂`
has its minimizer `(η′_ε(Q₂), µ_ε(Q₂))`, the shallow update returns a finite vector `η₁`, and
`‖η₁ − η′_ε(P)‖₂ ≤ δ`. This is the reading under which the "max" is defined and finite. -/
theorem proposition_5 {X : Type*} [Fintype X] [Nonempty X] {R : Finset ℝ} {S : Set (R → X → ℝ)}
    (hS : IsStructureSet S) {ε : ℝ} (hε : 0 < ε) {P : R → X → ℝ} (hP : P ∈ PPrime S) :
    (∃ ηP μP, IsDUSol S P ε ηP μP) ∧
    ∀ (ηP : X → ℝ) (μP : X → DualVec R X), IsDUSol S P ε ηP μP →
      ∀ δ : ℝ, 0 < δ → ∃ κ : ℝ, 0 < κ ∧
        ∀ Q₁ ∈ POmega R X, ∀ Q₂ ∈ POmega R X,
          (∀ r x, |Q₁ r x - P r x| ≤ κ) → (∀ r x, |Q₂ r x - P r x| ≤ κ) →
          ∃ (η₂ : X → ℝ) (μ₂ : X → DualVec R X), IsDUSol S Q₂ ε η₂ μ₂ ∧
            ∃ η₁ : X → ℝ, shallowUpdate S Q₁ η₂ μ₂ ε = some η₁ ∧
              Real.sqrt (∑ x, (η₁ x - ηP x) ^ 2) ≤ δ := by sorry

end StructBandit
