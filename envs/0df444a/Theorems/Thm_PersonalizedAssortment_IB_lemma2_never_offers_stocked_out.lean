-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_lemma2_never_offers_stocked_out
-- name    : PersonalizedAssortment.IB.lemma2_never_offers_stocked_out
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T01:57:47.08721+00:00
-- url     : https://prove2.me/theorems/0d5a0646-4687-466a-aad8-bccc11527694
-- title:
--   Lemma 2: inventory balancing never offers a stocked-out product
-- statement:
--   Let $r_i>0$ and $c_i\ge1$, and let $\mathcal S$ be a family of feasible assortments with $\emptyset\in\mathcal S$ that is closed under removing a product: $S\in\mathcal S$ and $j\in S$ imply $S\setminus\{j\}\in\mathcal S$. Suppose the choice models satisfy Assumption 1 (substitutability). Let $\Psi$ be a penalty function ($\Psi:[0,1]\to[0,1]$ increasing, $\Psi(0)=0$, $\Psi(1)=1$) and let $S^t(\cdot)$ be an inventory-balancing selection rule. That rule maximizes the index and, among the maximizers, has the fewest products. Then for every period $t$ and every inventory vector $0\le I\le c$,
--   $$i\in S^t(I)\;\Longrightarrow\;I_i>0 .$$
--   In words, the algorithm never offers an assortment that contains a product with zero remaining inventory.
--
--   Lemma 2 shows that inventory balancing respects the capacity constraints: it never tries to sell a unit it does not have.
--
--   **Formalization Note** The paper proves Lemma 2 in its online appendix and states it under Assumption 1 only. Closure of $\mathcal S$ under removing a product is added, because without it the lemma is false. For example, take $\mathcal S=\{\emptyset,\{1,2\}\}$ with product $1$ stocked out and product $2$ in stock with positive index: the rule must offer $\{1,2\}$. Every example family in the paper (cardinality, budget and shelf-space constraints) is closed under removal. The claim is made for every inventory vector between $0$ and $c$, which covers every state the process can reach.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1538, Lemma 2

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
import Definitions.Def_PersonalizedAssortment_IB_InventoryBalancing

namespace PersonalizedAssortment.IB

/-- Lemma 2 (p. 1538): under Assumption 1, the inventory-balancing algorithm never offers an
assortment containing a product with zero remaining inventory. Stated for every inventory vector
`I ≤ c` and every period. Added hypothesis `hdel`: the feasible family is closed under removing a
product (without it the lemma is false). -/
theorem lemma2_never_offers_stocked_out {n : ℕ} {Z : Type*} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (c : Fin n → ℕ) (hc : ∀ i, 0 < c i) (𝒮 : Finset (Finset (Fin n)))
    (h𝒮 : ∅ ∈ 𝒮) (hdel : ∀ S ∈ 𝒮, ∀ j ∈ S, S.erase j ∈ 𝒮) (φ : Z → ChoiceModel n)
    (hsub : Substitutable 𝒮 φ) (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ) {T : ℕ} (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (hsel : IsIBRule Ψ r c 𝒮 φ z sel)
    (t : Fin T) (I : Fin n → ℕ) (hI : ∀ i, I i ≤ c i) :
    ∀ i ∈ sel t I, 0 < I i := by sorry

end PersonalizedAssortment.IB
