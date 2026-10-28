-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_dual_certificate_feasible
-- name    : PersonalizedAssortment.IB.dual_certificate_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:56:48.836344+00:00
-- url     : https://prove2.me/theorems/d1241db8-6c63-4940-82b4-62f981b2e3f1
-- title:
--   The inventory-balancing dual certificate $(\lambda,\theta)$ is feasible for $\mathrm{Dual}(\{z_t\})$
-- statement:
--   Let $r_i>0$ and $c_i\ge1$, let $\emptyset\in\mathcal S$, and let $\Psi$ be a penalty function ($\Psi:[0,1]\to[0,1]$ increasing, $\Psi(0)=0$, $\Psi(1)=1$). Let $S^t(\cdot)$ be an inventory-balancing selection rule. Consider any inventory path $c=I^0\ge I^1\ge\dots\ge I^T$, compared coordinatewise. Define
--   $$\theta_i=r_i\big(1-\Psi(I_i^T/c_i)\big),\qquad \lambda^t=\sum_{i\in S^t}r_i\,\Psi(I_i^{t-1}/c_i)\,\varphi_i^{z_t}(S^t),\quad S^t=S^t(I^{t-1}).$$
--   Then $(\lambda,\theta)$ is feasible for $\mathrm{Dual}(\{z_t\}_{t=1}^T)$:
--
--   1. $\lambda^t\ge\sum_{i=1}^n\varphi_i^{z_t}(S)(r_i-\theta_i)$ for every period $t$ and every $S\in\mathcal S$;
--   2. $\theta_i\ge0$ for every product $i$.
--
--   Every realized path of the inventory process is non-increasing and starts at $c$, so the certificate is dual feasible with probability one. The certificate is what links the algorithm to the benchmark LP.
--
--   **Formalization Note** The paper writes the chain of inequalities only at $S=S^t$. Feasibility means every constraint $S\in\mathcal S$ holds, and that is what is stated.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1548, Section A.3, proof of Theorem 1 (construction of theta_i, lambda^t and the display showing dual feasibility)

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
import Definitions.Def_PersonalizedAssortment_IB_PrimalLP
import Definitions.Def_PersonalizedAssortment_IB_InventoryBalancing

namespace PersonalizedAssortment.IB

/-- §A.3, p. 1548: along any inventory path `c = I 0 ≥ I 1 ≥ ⋯ ≥ I T` on which the
inventory-balancing rule is followed, `θ_i = r_i (1 - Ψ(I_i^T/c_i))` and
`λ^t = ∑_{i ∈ S^t} r_i Ψ(I_i^{t-1}/c_i) φ_i^{z_t}(S^t)` form a feasible solution of
`Dual({z_t})`: every constraint, for every period and every `S ∈ 𝒮`, holds. -/
theorem dual_certificate_feasible {n : ℕ} {Z : Type*} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (c : Fin n → ℕ) (hc : ∀ i, 0 < c i) (𝒮 : Finset (Finset (Fin n))) (h𝒮 : ∅ ∈ 𝒮)
    (φ : Z → ChoiceModel n) (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ) {T : ℕ} (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (hsel : IsIBRule Ψ r c 𝒮 φ z sel)
    (I : ℕ → Fin n → ℕ) (hI0 : I 0 = c) (hmono : ∀ t < T, ∀ i, I (t + 1) i ≤ I t i) :
    DualFeasible r 𝒮 φ z (fun t => lamIB Ψ r c φ z sel t (I t.val)) (thetaIB Ψ r c (I T)) := by sorry

end PersonalizedAssortment.IB
