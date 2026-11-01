-- Prove2me | Theorems.Thm_StrategicNRM_lemma_1_ii
-- name    : StrategicNRM.lemma_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:33.913625+00:00
-- url     : https://prove2.me/theorems/64d831fc-c278-4e3d-8f9a-40c8d563c5d6
-- title:
--   Lemma 1(ii), p.10 (corrected: an interim inequality replaces the printed path-by-path equality)
-- statement:
--   Let $\theta$ be an admissible policy and $(\sigma,\text{play})$ an equilibrium under $\theta$. For every type $\phi\in\Phi$ and product $j$, writing $\phi_{j,0}$ for $\phi$ with valuation $0$ for product $j$,
--
--   $$
--   E_{-\phi}\big[U(\phi,y_\phi)\,(1-a^j_\phi)\big]\le E_{-\phi}\big[U(\phi_{j,0},y_{\phi_{j,0}})\big].
--   $$
--
--   In words: whatever $\phi$ earns on the event that he does not get product $j$ is available to a customer who does not value $j$ at all. This is the only use the revenue bound makes of the fact.
--
--   Differences from the source:
--   - correction: if a^{π,j}_φ = 0, then U(φ, y^π_φ) = U(φ_{j,0}, y^π_{φ_{j,0}}) → E₋φ[U(φ, y_φ)(1 − aʲ_φ)] ≤ E₋φ[U(φ_{j,0}, y_{φ_{j,0}})]; reason: the printed equality is false: n = 2, A = 0, T = 2, Exp(1) valuations, d = (0,1), π² ≡ 0, π¹ = ∞ on [0,1) and on [1,2] π¹ = 0 iff a sale occurred before 1; a type with v² = 1 and large v¹ waits and on the no-sale event buys product 2 at time 1 with utility e⁻¹, while φ_{1,0} buys at 0 with utility 1
--   - generalization: customers play a symmetric Markov Perfect Equilibrium: each maximizes E[U | C_{t_φ}] over stopping and purchasing rules → the symmetric rule maximizes, for every type, the unconditional expected utility over feasible rules with integrable payoff, with no Markov or perfection restriction on the rule; reason: the printed best response implies this one by the tower property, and every symmetric Markov Perfect Equilibrium is such a profile, so the hypothesis is weaker and the conclusion covers the printed equilibria
--   - reading: the expectations E₋φ[U] and E[Σ p] are written without comment → IsEquilibrium carries joint measurability of the outcome, integrability of the price for each type, and integrability of Σ|p| over the crowd; reason: these say that the printed expectations are defined; a Bochner integral of a non-integrable function would otherwise be 0
--   - reading: §2 does not say what happens when several customers buy at one instant with too few units left → attempts at one instant are served in the order (purchase time, arrival, index) and a rationed customer exits with nothing; reason: the literal model oversells at a price jump, and then Theorem 1 fails; plays without excess demand at a tie are unchanged, while assuming no overselling would exclude every policy with a price jump
--   - generalization: π is F_t-progressive → a policy is any function of the sales strictly before t and of t, with no measurability condition on the policy; Non-negative inventory is asked at every sales record; reason: the sales are all of F_t, so every printed policy is one of these (its values on sales records that cannot occur may be set to ∞ without changing any play); the measurability the proof uses is in IsEquilibrium
--   - encoding: a Poisson process of rate λ on [0,T] of customers with i.i.d. marks → a Poisson(λT) number of i.i.d. types with uniform arrival, and E₋φ as integration over a fresh crowd; reason: the two are the same law; removing a point from a Poisson process leaves a Poisson process
--   - encoding: x₀ ∈ ℝᵐ → x₀ ∈ ℕᵐ; reason: p.6 says resources are indivisible, so non-integer stock has no meaning
--   - encoding: prices in ℝ with ∞ for a sold-out product → prices in WithTop ℝ, read through untopD 0 on a purchase, which is at a finite price; reason: Lean convention; same instances
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §3.1, Lemma 1(ii), p.10

import Mathlib
import Definitions.Def_StrategicNRM_Equilibrium

open MeasureTheory
open scoped ENNReal NNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- Chen & Trichakis, SSRN 2959489 (version of May 29, 2018), Lemma 1(ii), p.10, **corrected**.
Printed: if `a^{π,j}_φ = 0`, then `U(φ, yᵖ_φ) = U(φ_{j,0}, yᵖ_{φ_{j,0}})`, for all `j`. That is false
(a customer with a large `vʲ` may wait for product `j`, and end up at a later and worse purchase of
another product, while `φ_{j,0}` buys at once). The interim inequality here is what the argument
needs: `E₋φ[U(φ, yᵖ_φ)(1 − a^{π,j}_φ)] ≤ E₋φ[U(φ_{j,0}, yᵖ_{φ_{j,0}})]`. -/
theorem lemma_1_ii (I : Instance n m) {θ : Policy n} (_hθ : Admissible I θ) {P : Profile n}
    (hP : IsEquilibrium I θ P) {φ : CType n} (hφ : I.IsType φ) (j : Fin n) :
    ∫ c, utility φ (P.y I θ φ c) * (1 - alloc (P.y I θ φ c).2.1 j) ∂I.law ≤
      ∫ c, utility (withVal φ j 0) (P.y I θ (withVal φ j 0) c) ∂I.law := by sorry

end StrategicNRM
