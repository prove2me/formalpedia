-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_expected_dual_value
-- name    : PersonalizedAssortment.IB.expected_dual_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T01:56:52.37898+00:00
-- url     : https://prove2.me/theorems/5ae17969-b846-4662-bb51-354e1fc7e349
-- title:
--   Expected dual value: $\mathbb E[\sum_t\lambda^t]=\mathbb E[\sum_i r_i\sum_{k=I_i^T+1}^{c_i}\Psi(k/c_i)]$
-- statement:
--   Let $\Psi$ be any function with $\Psi(0)=0$. Let $S^t(\cdot)$ be any selection rule and let $I^0=c,I^1,\dots,I^T$ be the inventory process it generates. Define $\lambda^t=\sum_{i\in S^t}r_i\Psi(I_i^{t-1}/c_i)\varphi_i^{z_t}(S^t)$ with $S^t=S^t(I^{t-1})$. Then
--   $$\mathbb E\Big[\sum_{t=1}^T\lambda^t\Big]\;=\;\mathbb E\Big[\sum_{i=1}^n r_i\sum_{k=I_i^T+1}^{c_i}\Psi\!\left(\frac k{c_i}\right)\Big].$$
--
--   The identity expresses the expected objective of the dual certificate through the final inventory alone. It is the computation that precedes the weak-duality bound in the proof of Theorem 1.
--
--   **Formalization Note** $\mathbb E\big[\sum_t\lambda^t\big]$ is written as $\sum_t\mathbb E[\lambda^t(I^{t-1})]$. The paper uses Lemma 2 to know that a product with zero inventory is never offered. Here the dynamics $I_i^t=\max\{I_i^{t-1}-1,0\}$ are used instead, together with $\Psi(0)=0$: a stocked-out product contributes $0$ to both sides whether or not it is offered. So the identity holds for every selection rule, and neither Assumption 1 nor Lemma 2 is needed.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, pp. 1548-1549, Section A.3, proof of Theorem 1, display beginning 'E[sum_t lambda^t] =' and the sentences after it

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_InventoryBalancing

namespace PersonalizedAssortment.IB

/-- The expected-dual display of §A.3 (pp. 1548–1549):
`𝔼[∑_{t=1}^T λ^t] = 𝔼[∑_{i=1}^n r_i ∑_{k=I_i^T+1}^{c_i} Ψ(k/c_i)]`, where `λ^t` is evaluated at the
inventories `I^{t-1}` at the start of the period and the right side at the final inventories
`I^T`. -/
theorem expected_dual_value {n : ℕ} {Z : Type*} (r : Fin n → ℝ) (c : Fin n → ℕ)
    (φ : Z → ChoiceModel n) (Ψ : ℝ → ℝ) (hΨ0 : Ψ 0 = 0) {T : ℕ} (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) :
    ∑ t : Fin T, expectInv φ z sel c t.val t.isLt.le (lamIB Ψ r c φ z sel t) =
      expectInv φ z sel c T le_rfl
        (fun I => ∑ i : Fin n, r i * ∑ k ∈ Finset.Ioc (I i) (c i), Ψ ((k : ℝ) / (c i : ℝ))) := by sorry

end PersonalizedAssortment.IB
