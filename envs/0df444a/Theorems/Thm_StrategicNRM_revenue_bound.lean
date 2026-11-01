-- Prove2me | Theorems.Thm_StrategicNRM_revenue_bound
-- name    : StrategicNRM.revenue_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:39.556257+00:00
-- url     : https://prove2.me/theorems/3a0944d1-4354-411d-9151-c056feac55d1
-- title:
--   Theorem 1 (Revenue Bound), p.22 — $J^\pi\le J^\star\le\bar J^1$
-- statement:
--   Consider the seller of $n$ products built from $m$ capacitated resources, facing customers who arrive as a Poisson process over $[0,T]$ with private valuations for every product and private decay rates, and who choose both when and what to buy. Suppose that the virtual value $v-\bar F_j(v)/f_j(v)$ of each product is non-decreasing (Assumption 1). Then for any admissible dynamic pricing policy $\pi$ and any equilibrium of the customers under it,
--
--   $$
--   J^\pi\le J^\star\le\bar J^1,
--   $$
--
--   where $\bar J^1$ is the optimal value of the deterministic problem
--
--   $$
--   \max\ \lambda T\sum_{j=1}^n q^j\bar F_j(q^j)\quad\text{s.t.}\quad\sum_{j=1}^n\bar F_j(q^j)\le 1,\qquad\lambda T\sum_{j=1}^n A_{ij}\bar F_j(q^j)\le x_0^i\ \ \forall i.
--   $$
--
--   The bound holds for arbitrary price paths and multi-dimensional private information, and it is the stepping stone of the paper's analysis of static pricing.
--
--   **Formalization Note** The theorem has no moment hypothesis, no restriction on $n$ or $m$, and no sign condition on prices. Inventory is enforced by the rationing inside a play.
--
--   Differences from the source:
--   - reading: §2 does not say what happens when several customers buy at one instant with too few units left → attempts at one instant are served in the order (purchase time, arrival, index) and a rationed customer exits with nothing; reason: the literal model oversells at a price jump, and then Theorem 1 fails; plays without excess demand at a tie are unchanged, while assuming no overselling would exclude every policy with a price jump
--   - generalization: customers play a symmetric Markov Perfect Equilibrium: each maximizes E[U | C_{t_φ}] over stopping and purchasing rules → the symmetric rule maximizes, for every type, the unconditional expected utility over feasible rules with integrable payoff, with no Markov or perfection restriction on the rule; reason: the printed best response implies this one by the tower property, and every symmetric Markov Perfect Equilibrium is such a profile, so the hypothesis is weaker and the conclusion covers the printed equilibria
--   - reading: the expectations E₋φ[U] and E[Σ p] are written without comment → IsEquilibrium carries joint measurability of the outcome, integrability of the price for each type, and integrability of Σ|p| over the crowd; reason: these say that the printed expectations are defined; a Bochner integral of a non-integrable function would otherwise be 0
--   - generalization: J^π for the equilibrium of π → J for every equilibrium of θ, and J⋆ over all pairs; reason: the paper proves neither existence nor uniqueness (footnote 2, p.8); a selected equilibrium is one of these
--   - generalization: π is F_t-progressive → a policy is any function of the sales strictly before t and of t, with no measurability condition on the policy; Non-negative inventory is asked at every sales record; reason: the sales are all of F_t, so every printed policy is one of these (its values on sales records that cannot occur may be set to ∞ without changing any play); the measurability the proof uses is in IsEquilibrium
--   - reading: Assumption 1: v − F̄ⱼ(v)/fⱼ(v) non-decreasing for all v ≥ 0 → fⱼ > 0 a.e. on the interior of the support, and the virtual value non-decreasing where fⱼ > 0 there; reason: p.18 names the uniform distribution, for which the literal assumption is meaningless
--   - encoding: q ∈ ℝⁿ in (18) → q ∈ [0,∞]ⁿ with ∞ · 0 = 0; reason: a negative price is dominated by 0 and ∞ encodes F̄ⱼ = 0; the suprema agree whenever the real problem is feasible, and with x₀ⁱ = 0 on unbounded support the real problem would be infeasible
--   - encoding: a Poisson process of rate λ on [0,T] of customers with i.i.d. marks → a Poisson(λT) number of i.i.d. types with uniform arrival, and E₋φ as integration over a fresh crowd; reason: the two are the same law; removing a point from a Poisson process leaves a Poisson process
--   - encoding: x₀ ∈ ℝᵐ → x₀ ∈ ℕᵐ; reason: p.6 says resources are indivisible, so non-integer stock has no meaning
--   - encoding: prices in ℝ with ∞ for a sold-out product → prices in WithTop ℝ, read through untopD 0 on a purchase, which is at a finite price; reason: Lean convention; same instances
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §3.2.2, Theorem 1 (Revenue Bound), p.22, under Assumption 1, p.18

import Mathlib
import Definitions.Def_StrategicNRM_Equilibrium
import Definitions.Def_StrategicNRM_Fluid

open MeasureTheory
open scoped ENNReal NNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- Chen & Trichakis, SSRN 2959489 (version of May 29, 2018), Theorem 1 (Revenue Bound), p.22:
under Assumption 1, for any dynamic pricing policy `π ∈ Π`, `Jᵖ ≤ J⋆ ≤ J̄¹`, where `J̄¹` is the
optimal value of the fluid problem (18). -/
theorem revenue_bound (I : Instance n m) (hA : I.Assumption1) {θ : Policy n}
    (hθ : Admissible I θ) {P : Profile n} (hP : IsEquilibrium I θ P) :
    ((J I θ P : ℝ) : EReal) ≤ Jstar I ∧ Jstar I ≤ I.Jbar 1 := by sorry

end StrategicNRM
