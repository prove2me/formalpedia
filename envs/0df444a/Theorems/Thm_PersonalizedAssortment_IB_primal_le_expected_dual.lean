-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_primal_le_expected_dual
-- name    : PersonalizedAssortment.IB.primal_le_expected_dual
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:57:18.909633+00:00
-- url     : https://prove2.me/theorems/212fabd2-d057-4f6e-8641-d06d1e30b823
-- title:
--   Weak-duality bound: $\mathrm{Primal}\le\mathbb E[\sum_i r_i(\sum_{k=I_i^T+1}^{c_i}\Psi(k/c_i)+c_i(1-\Psi(I_i^T/c_i)))]$
-- statement:
--   Let $r_i>0$ and $c_i\ge1$, let $\emptyset\in\mathcal S$, and let $\Psi$ be a penalty function ($\Psi:[0,1]\to[0,1]$ increasing, $\Psi(0)=0$, $\Psi(1)=1$). Let $S^t(\cdot)$ be an inventory-balancing selection rule and let $I^T$ be the final inventory of the process it generates. Then every feasible solution $y$ of $\mathrm{Primal}(\{z_t\}_{t=1}^T)$ satisfies
--   $$\sum_{t=1}^T\sum_{S\in\mathcal S}\sum_{i=1}^n r_i\,\varphi_i^{z_t}(S)\,y^t(S)\;\le\;\mathbb E\Big[\sum_{i=1}^n r_i\Big(\sum_{k=I_i^T+1}^{c_i}\Psi\!\left(\frac k{c_i}\right)+c_i\big(1-\Psi(I_i^T/c_i)\big)\Big)\Big].$$
--
--   The right side is the expected objective of the dual certificate $(\lambda,\theta)$. The bound combines dual feasibility with probability one, weak duality and the expected-dual identity. It is the upper bound on the benchmark that the proof of Theorem 1 compares with the algorithm's revenue.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1549, Section A.3, proof of Theorem 1, first display ('Since theta_i and lambda^t are dual feasible, it follows from the weak duality theorem that ...')

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
import Definitions.Def_PersonalizedAssortment_IB_PrimalLP
import Definitions.Def_PersonalizedAssortment_IB_InventoryBalancing

namespace PersonalizedAssortment.IB

/-- The weak-duality display of §A.3 (p. 1549): the objective of every feasible solution of
`Primal({z_t})` is at most
`𝔼[∑_{i=1}^n r_i (∑_{k=I_i^T+1}^{c_i} Ψ(k/c_i) + c_i (1 - Ψ(I_i^T/c_i)))]`, the expectation being
over the final inventories `I^T` of the inventory-balancing algorithm. -/
theorem primal_le_expected_dual {n : ℕ} {Z : Type*} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (c : Fin n → ℕ) (hc : ∀ i, 0 < c i) (𝒮 : Finset (Finset (Fin n))) (h𝒮 : ∅ ∈ 𝒮)
    (φ : Z → ChoiceModel n) (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ) {T : ℕ} (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (hsel : IsIBRule Ψ r c 𝒮 φ z sel)
    (y : Fin T → Finset (Fin n) → ℝ) (hy : PrimalFeasible c 𝒮 φ z y) :
    primalObj r 𝒮 φ z y ≤
      expectInv φ z sel c T le_rfl (fun I => ∑ i : Fin n, r i *
        (∑ k ∈ Finset.Ioc (I i) (c i), Ψ ((k : ℝ) / (c i : ℝ)) +
          (c i : ℝ) * (1 - Ψ ((I i : ℝ) / (c i : ℝ))))) := by sorry

end PersonalizedAssortment.IB
