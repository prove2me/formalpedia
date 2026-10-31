-- Prove2me | Theorems.Thm_SupplierLearning_lemma_1_b
-- name    : SupplierLearning.lemma_1_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:01.101908+00:00
-- url     : https://prove2.me/theorems/c933e6a5-3609-41e0-b0b7-65ee59800e60
-- title:
--   Lemma 1(b) — first best in regime $\mathcal P^{\mathrm{PP}}$ (corrected: assumes $\delta\rho(r^\theta)^2<4$)
-- statement:
--   Fix a type $\theta$ with $\delta\rho(r^\theta)^2<4$, and let $(q_1^{\theta|\mathrm{PP}},q_2^{\theta1|\mathrm{PP}},q_2^{\theta0|\mathrm{PP}})$ be the quantities
--   $$
--   q_1^{\theta|\mathrm{PP}}=\frac{2(a_1-c^\theta)+\delta\rho r^\theta(a_2-c^\theta)}{4-\delta\rho(r^\theta)^2},\qquad q_2^{\theta\Lambda|\mathrm{PP}}=\frac{2(a_2-c^\theta)+\Lambda r^\theta(a_1-c^\theta)}{4-\delta\Lambda\rho(r^\theta)^2}.
--   $$
--   Then:
--
--   1. these quantities are the unique maximizer of the channel surplus $W_\theta$ on $\mathbb R^3$;
--   2. the term with these quantities and marginal-cost payments $p_t^{s|\mathrm{PP}}=c_t^sq_t^{s|\mathrm{PP}}$ gives the supplier payoff $0$ and the buyer the surplus $W_\theta$ at the maximizer;
--   3. every term satisfying the participation constraint gives the buyer at most this value, and equality forces these quantities and zero supplier payoff.
--
--   This is the full-information benchmark. The proof of Proposition 1 uses it for type $\ell$, whose quantities stay at this first best.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - correction: Lemma 1(b) states no second-order condition → hypothesis δρ(r^θ)² < 4; reason: the printed optimum need not exist: at a₁ = a₂ = 100, c^θ = 10, r^θ = 3, δ = ρ = 9/10 the surplus along (q, (90 + 3q)/2, 45) is unbounded (δρ(r^θ)² = 7.29)
--   - reading: the optimal contract of (P^PP), one contract for all types → the statement for one type θ at a time, over all real quantities; reason: with θ public the problem separates by type, and (P^PP) on p.9 lists only IR
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Lemma 1(b), p.9; proof, App. p.3

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Params_rate
import Definitions.Def_SupplierLearning_Term
import Definitions.Def_SupplierLearning_Params_termBuyerPayoff
import Definitions.Def_SupplierLearning_Params_typeSurplus
import Definitions.Def_SupplierLearning_Params_firstBestOne
import Definitions.Def_SupplierLearning_Params_firstBestTwo
import Definitions.Def_SupplierLearning_Params_firstBestTerm
import Definitions.Def_SupplierLearning_Params_publicPayoff

namespace SupplierLearning

/-- **Lemma 1(b) — first best in regime P^{PP} (corrected: assumes δρ(r^θ)^2<4).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Lemma 1(b), p.9; proof, App. p.3 (PDF p.9, 35).

**Formalization Note.** The hypothesis `δρ(r^θ)² < 4` is correction C2. The maximum is over all real quantities, as (P^PP) on p.9 has only IR; nonnegativity and (C) are then consequences when the first best satisfies them. The contract is stated one type at a time, since with public types the problem separates. -/
theorem lemma_1_b (P : Params) (hP : P.Standing) (θ : SupplierType)
    (hθ : P.δ * P.ρ * P.rate θ ^ 2 < 4) :
    (∀ q y z,
      P.typeSurplus θ q y z ≤
          P.typeSurplus θ (P.firstBestOne θ) (P.firstBestTwo θ true) (P.firstBestTwo θ false) ∧
        (P.typeSurplus θ q y z =
            P.typeSurplus θ (P.firstBestOne θ) (P.firstBestTwo θ true) (P.firstBestTwo θ false) →
          q = P.firstBestOne θ ∧ y = P.firstBestTwo θ true ∧ z = P.firstBestTwo θ false)) ∧
    P.publicPayoff θ (P.firstBestTerm θ) = 0 ∧
    P.termBuyerPayoff (P.firstBestTerm θ) =
      P.typeSurplus θ (P.firstBestOne θ) (P.firstBestTwo θ true) (P.firstBestTwo θ false) ∧
    ∀ t : Term, 0 ≤ P.publicPayoff θ t →
      P.termBuyerPayoff t ≤ P.termBuyerPayoff (P.firstBestTerm θ) ∧
        (P.termBuyerPayoff t = P.termBuyerPayoff (P.firstBestTerm θ) →
          t.q₁ = P.firstBestOne θ ∧ (∀ Λ, t.q₂ Λ = P.firstBestTwo θ Λ) ∧ P.publicPayoff θ t = 0) := by sorry

end SupplierLearning
