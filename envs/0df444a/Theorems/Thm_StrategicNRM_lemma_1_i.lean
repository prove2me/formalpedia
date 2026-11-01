-- Prove2me | Theorems.Thm_StrategicNRM_lemma_1_i
-- name    : StrategicNRM.lemma_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:44.599808+00:00
-- url     : https://prove2.me/theorems/b539fe29-f83b-418d-91dc-acef708d6aaf
-- title:
--   Lemma 1(i), p.9 — a customer's utility is non-negative almost surely
-- statement:
--   Let $\theta$ be an admissible policy and $(\sigma,\text{play})$ an equilibrium under $\theta$. For every type $\phi\in\Phi$,
--
--   $$
--   U(\phi,y_\phi)\ge 0
--   $$
--
--   almost surely in the crowd of the other customers.
--
--   This is the (IR) constraint of the mechanism that a policy induces: a customer can always decline.
--
--   Differences from the source:
--   - generalization: customers play a symmetric Markov Perfect Equilibrium: each maximizes E[U | C_{t_φ}] over stopping and purchasing rules → the symmetric rule maximizes, for every type, the unconditional expected utility over feasible rules with integrable payoff, with no Markov or perfection restriction on the rule; reason: the printed best response implies this one by the tower property, and every symmetric Markov Perfect Equilibrium is such a profile, so the hypothesis is weaker and the conclusion covers the printed equilibria
--   - reading: the expectations E₋φ[U] and E[Σ p] are written without comment → IsEquilibrium carries joint measurability of the outcome, integrability of the price for each type, and integrability of Σ|p| over the crowd; reason: these say that the printed expectations are defined; a Bochner integral of a non-integrable function would otherwise be 0
--   - reading: §2 does not say what happens when several customers buy at one instant with too few units left → attempts at one instant are served in the order (purchase time, arrival, index) and a rationed customer exits with nothing; reason: the literal model oversells at a price jump, and then Theorem 1 fails; plays without excess demand at a tie are unchanged, while assuming no overselling would exclude every policy with a price jump
--   - generalization: π is F_t-progressive → a policy is any function of the sales strictly before t and of t, with no measurability condition on the policy; Non-negative inventory is asked at every sales record; reason: the sales are all of F_t, so every printed policy is one of these (its values on sales records that cannot occur may be set to ∞ without changing any play); the measurability the proof uses is in IsEquilibrium
--   - encoding: a Poisson process of rate λ on [0,T] of customers with i.i.d. marks → a Poisson(λT) number of i.i.d. types with uniform arrival, and E₋φ as integration over a fresh crowd; reason: the two are the same law; removing a point from a Poisson process leaves a Poisson process
--   - encoding: x₀ ∈ ℝᵐ → x₀ ∈ ℕᵐ; reason: p.6 says resources are indivisible, so non-integer stock has no meaning
--   - encoding: prices in ℝ with ∞ for a sold-out product → prices in WithTop ℝ, read through untopD 0 on a purchase, which is at a finite price; reason: Lean convention; same instances
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §3.1, Lemma 1(i), p.9

import Mathlib
import Definitions.Def_StrategicNRM_Equilibrium

open MeasureTheory
open scoped ENNReal NNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- Chen & Trichakis, SSRN 2959489 (version of May 29, 2018), Lemma 1(i), p.9: under any policy in
`Π`, a customer derives non-negative utility, `U(φ, yᵖ_φ) ≥ 0`, almost surely in the others. -/
theorem lemma_1_i (I : Instance n m) {θ : Policy n} (_hθ : Admissible I θ) {P : Profile n}
    (hP : IsEquilibrium I θ P) {φ : CType n} (hφ : I.IsType φ) :
    ∀ᵐ c ∂I.law, 0 ≤ utility φ (P.y I θ φ c) := by sorry

end StrategicNRM
