-- Prove2me | Theorems.Thm_StrategicNRM_lemma_2
-- name    : StrategicNRM.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:52.966391+00:00
-- url     : https://prove2.me/theorems/eae42b49-c384-4ce5-80d7-3673d6a2d938
-- title:
--   Lemma 2, p.13 (corrected: against problem (5) with its three changes) — the game embeds in the mechanism problem
-- statement:
--   For any admissible policy $\theta$ and any equilibrium under it,
--
--   $$
--   J^\pi\le J^{\mathrm{md}},\qquad\text{and}\qquad J^\star\le J^{\mathrm{md}},
--   $$
--
--   where $J^{\mathrm{md}}$ is the value of the mechanism design problem (5), as corrected.
--
--   The mechanism is $y_\phi(c)$, the outcome of a customer of type $\phi$ against the others $c$. The content is that a customer is silent: the plays of a crowd and of the crowd without customer $i$ agree strictly before $i$ in the order, so the path and the rationing that $i$ faces are those of the others, and these others form a fresh Poisson crowd.
--
--   Differences from the source:
--   - correction: problem (5) of p.12, with (IC) for t_φ̂ ∈ [t_φ, T], the last line U(φ, y_φ) = U(φ_{j,0}, y_{φ_{j,0}}) on a^j_φ = 0, and p_φ ≥ 0 in Y → (IC) for t_φ̂ = t_φ, the last line replaced by the inequality of Lemma 1(ii), and no constraint p_φ ≥ 0; reason: the mechanism of a policy need not satisfy the printed constraints: the instance of Lemma 1(ii) breaks the last line; a later report keeps the true earlier priority under rationing by arrival; Π has no sign condition. Each change enlarges the feasible set. The printed Lemma 2 itself fails in the printed model, where simultaneous buyers are all served: for n = m = 1, x₀ = 1, Exp(1) valuations, d = 0, T = 2 and π = ∞ on [0,1), 1 after (∞ once sold out), every waiting customer with v ≥ 1 buys at time 1, so Jπ ≥ λ/e, while Lemmas 3, 4(b) and 6 bound the printed Jᵐᵈ by J̄¹ = log(2λ) < λ/e for large λ
--   - generalization: customers play a symmetric Markov Perfect Equilibrium: each maximizes E[U | C_{t_φ}] over stopping and purchasing rules → the symmetric rule maximizes, for every type, the unconditional expected utility over feasible rules with integrable payoff, with no Markov or perfection restriction on the rule; reason: the printed best response implies this one by the tower property, and every symmetric Markov Perfect Equilibrium is such a profile, so the hypothesis is weaker and the conclusion covers the printed equilibria
--   - reading: the expectations E₋φ[U] and E[Σ p] are written without comment → IsEquilibrium carries joint measurability of the outcome, integrability of the price for each type, and integrability of Σ|p| over the crowd; reason: these say that the printed expectations are defined; a Bochner integral of a non-integrable function would otherwise be 0
--   - reading: §2 does not say what happens when several customers buy at one instant with too few units left → attempts at one instant are served in the order (purchase time, arrival, index) and a rationed customer exits with nothing; reason: the literal model oversells at a price jump, and then Theorem 1 fails; plays without excess demand at a tie are unchanged, while assuming no overselling would exclude every policy with a price jump
--   - generalization: J^π for the equilibrium of π → J for every equilibrium of θ, and J⋆ over all pairs; reason: the paper proves neither existence nor uniqueness (footnote 2, p.8); a selected equilibrium is one of these
--   - reading: the class Y of p.11–12: τ_φ a G_t-stopping time, (a_φ, p_φ) G_τ-measurable, and the expectations of (5) written without comment → IsFeasibleMechanism: y φ depends on the others only through the reports with arrival ≤ τ (index-ordered, on crowds of types), joint measurability of the outcome, integrability of each price and of Σ|p| over the crowd; reason: these say that y is causal and that the printed expectations are defined; a Bochner integral of a non-integrable function would otherwise be 0
--   - generalization: π is F_t-progressive → a policy is any function of the sales strictly before t and of t, with no measurability condition on the policy; Non-negative inventory is asked at every sales record; reason: the sales are all of F_t, so every printed policy is one of these (its values on sales records that cannot occur may be set to ∞ without changing any play); the measurability the proof uses is in IsEquilibrium
--   - encoding: a Poisson process of rate λ on [0,T] of customers with i.i.d. marks → a Poisson(λT) number of i.i.d. types with uniform arrival, and E₋φ as integration over a fresh crowd; reason: the two are the same law; removing a point from a Poisson process leaves a Poisson process
--   - encoding: x₀ ∈ ℝᵐ → x₀ ∈ ℕᵐ; reason: p.6 says resources are indivisible, so non-integer stock has no meaning
--   - encoding: prices in ℝ with ∞ for a sold-out product → prices in WithTop ℝ, read through untopD 0 on a purchase, which is at a finite price; reason: Lean convention; same instances
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §3.2.2, Lemma 2, p.13

import Mathlib
import Definitions.Def_StrategicNRM_Equilibrium
import Definitions.Def_StrategicNRM_Mechanism

open MeasureTheory
open scoped ENNReal NNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- Chen & Trichakis, SSRN 2959489 (version of May 29, 2018), Lemma 2, p.13, against problem (5)
as corrected in `IsDesignFeasible` and `IsFeasibleMechanism`: for any pricing policy `π ∈ Π`,
`Jᵖ ≤ Jᵐᵈ`, and `J⋆ ≤ Jᵐᵈ`. -/
theorem lemma_2 (I : Instance n m) {θ : Policy n} (_hθ : Admissible I θ) {P : Profile n}
    (hP : IsEquilibrium I θ P) :
    ((J I θ P : ℝ) : EReal) ≤ Jmd I ∧ Jstar I ≤ Jmd I := by sorry

end StrategicNRM
