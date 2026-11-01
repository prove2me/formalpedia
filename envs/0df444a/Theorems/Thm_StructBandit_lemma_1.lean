-- Prove2me | Theorems.Thm_StructBandit_lemma_1
-- name    : StructBandit.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:33:36.207531+00:00
-- url     : https://prove2.me/theorems/c3dc30d0-2f1b-4598-b2fb-981fdbc17d07
-- title:
--   Lemma 1 — weak duality $\mathrm{Dual}\le\mathrm{Dist}$ and strong duality for deceitful arms
-- statement:
--   (a) **Weak duality.** For every reward distribution $P\in\mathcal P_\Omega$, every arm $x'\in X$, every $\eta\ge0$ and every dual vector $\mu\in\mathbb R_+\times\mathbb R\times\mathcal K^\star$,
--
--   $$
--   \mathrm{Dual}(\eta,x',P;\mu)\le\mathrm{Dist}(\eta,x',P).
--   $$
--
--   (b) **Strong duality.** For every $P\in\mathcal P$ and every suboptimal deceitful arm $x'\in\tilde X_d(P)$,
--
--   $$
--   \mathrm{Dist}(\eta,x',P)=\sup_\mu\{\mathrm{Dual}(\eta,x',P;\mu):\ \mu\in\mathbb R_+\times\mathbb R\times\mathcal K^\star\}.
--   $$
--
--   Weak duality is what lets DUSA's sufficient-information test certify $\mathrm{Dist}\ge1+\epsilon$ without solving the semi-infinite program (7).
--
--   Differences from the source:
--
--   - reading: η unqualified in Lemma 1 → η ≥ 0; reason: η ≥ 0 is the domain of Dist in (6)–(7)
--   - reading: χ_{−∞}(η(x) − λ(r,x) − β − αr𝟙(x = x′) ≥ 0) in (14), with no index range → the constraint for every x ∈ X̃(P), r ∈ R; a log term is 0 if η(x)P(r,x) = 0 and −∞ if its argument is 0; reason: the range of the sum it closes, and the values the derivation of App. C.2 (p.43) gives at the boundary
--   - encoding: I, Dist, C, C̄, Rewmax, Dual, Dual‾ as extended-real optimal values ('max' over ρ ≥ 0 in (17) and 'max' in (8) included); SU := +∞ if (19) is infeasible → EReal values with inf ∅ = +∞, sup ∅ = −∞; SU returns Option (none = +∞), and none also when (19) is feasible but has no minimizer; reason: the source's conventions; a supremum need not be attained off the source's setting; (19) is an argmin, so nothing is defined without a minimizer; Lean's log 0 = 0 and x/0 = 0 decide no case
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Lemma 1, Eq. (15), p.22 (proof App. C.2)

import Mathlib
import Definitions.Def_StructBandit_lowerBound
import Definitions.Def_StructBandit_PPrime
import Definitions.Def_StructBandit_dualFn

open scoped BigOperators

namespace StructBandit

/-- **Lemma 1 (Dual Formulation of the Distance Function).**
Van Parys & Golrezaei, arXiv:2007.07302v3, Lemma 1, Eq. (15), p.22 (proof App. C.2).

(a) Weak duality: for any `P ∈ P_Ω`, any arm `x′ ∈ X`, any rates `η ≥ 0` and any feasible dual vector
`µ ∈ ℝ₊ × ℝ × K⋆`, `Dual(η,x′,P;µ) ≤ Dist(η,x′,P)`.
(b) Strong duality: for any `P ∈ 𝒫` and any suboptimal deceitful arm `x′ ∈ X̃d(P)`,
`Dist(η,x′,P) = sup_µ {Dual(η,x′,P;µ) : µ ∈ ℝ₊ × ℝ × K⋆}`.

**Formalization Note.** `η ≥ 0` is the domain of `Dist` in (6)–(7). Both sides are extended reals. -/
theorem lemma_1 {X : Type*} [Fintype X] [Nonempty X] {R : Finset ℝ} {S : Set (R → X → ℝ)}
    (hS : IsStructureSet S) :
    (∀ P ∈ POmega R X, ∀ x' : X, ∀ η : X → ℝ, (∀ x, 0 ≤ η x) →
        ∀ μ : DualVec R X, IsDualFeasible S μ → dualFn η x' P μ ≤ distFn S η x' P) ∧
    (∀ P ∈ S, ∀ x' ∈ deceitArms S P, ∀ η : X → ℝ, (∀ x, 0 ≤ η x) →
        distFn S η x' P = ⨆ (μ : DualVec R X) (_ : IsDualFeasible S μ), dualFn η x' P μ) := by sorry

end StructBandit
