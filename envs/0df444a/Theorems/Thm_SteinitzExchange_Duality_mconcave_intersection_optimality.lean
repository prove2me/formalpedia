-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_mconcave_intersection_optimality
-- name    : SteinitzExchange.Duality.mconcave_intersection_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:59:19.504976+00:00
-- url     : https://prove2.me/theorems/93c38767-157e-4348-81c8-107fd1831ed8
-- title:
--   Theorem 6.6 — the M-concave intersection theorem (optimality via a potential $p^*$)
-- statement:
--   Let $B_1,B_2\subseteq\mathbb Z^V$ be finite integral base sets, let $\omega_1:B_1\to\mathbb R$ and $\omega_2:B_2\to\mathbb R$ satisfy (EXC), and let $x^*\in B_1\cap B_2$. Then
--
--   $$\omega_1(x^*)+\omega_2(x^*)\ge\omega_1(x)+\omega_2(x)\qquad\forall x\in B_1\cap B_2$$
--
--   if and only if there exists $p^*\in\mathbb R^V$ such that
--
--   $$\omega_1[-p^*](x^*)\ge\omega_1[-p^*](x)\ \ \forall x\in B_1,\qquad \omega_2[p^*](x^*)\ge\omega_2[p^*](x)\ \ \forall x\in B_2,$$
--
--   where $\omega[p](x)=\omega(x)+\langle p,x\rangle$. Moreover, if $\omega_1$ and $\omega_2$ are integer-valued, there exists such a $p^*$ in $\mathbb Z^V$.
--
--   This is the optimality criterion for the M-concave intersection problem, which the paper cites from Murota's earlier work without proof; it gives part (P2) and the dual integrality of the duality theorem.
--
--   **Formalization Note.** The integral clause is stated as: if $\omega_1,\omega_2$ are integer-valued on $B_1,B_2$ and $x^*$ is optimal, some integral $p^*$ satisfies both inequalities (the "such a $p^*$" of the page).
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 296, Theorem 6.6 (citing [32, Theorem 4.1] = K. Murota, Submodular flow problem with a nonseparable cost function, Report 95843-OR, Univ. Bonn, 1995; proofs in [32], [28] (Valuated matroid intersection I, SIAM J. Discrete Math. 9 (1996)) or [35])

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange

namespace SteinitzExchange.Duality

/-- Murota 1996, p. 296, Theorem 6.6 (the M-concave intersection theorem, [32, Theorem 4.1]).
Let `B₁, B₂ ⊆ ℤ^V` be finite integral base sets, `ω₁ : B₁ → ℝ` and `ω₂ : B₂ → ℝ` satisfy (EXC),
and `x* ∈ B₁ ∩ B₂`. Then `ω₁(x*) + ω₂(x*) ≥ ω₁(x) + ω₂(x)` for all `x ∈ B₁ ∩ B₂` iff there is
`p* ∈ ℝ^V` with `ω₁[−p*](x*) ≥ ω₁[−p*](x)` for all `x ∈ B₁` and `ω₂[p*](x*) ≥ ω₂[p*](x)` for all
`x ∈ B₂`. Moreover, if `ω₁` and `ω₂` are integer-valued (and `x*` is optimal), such a `p*`
exists in `ℤ^V`. -/
theorem mconcave_intersection_optimality {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω₁ ω₂ : (V → ℤ) → ℝ) (hω₁ : SatisfiesEXC B₁ ω₁) (hω₂ : SatisfiesEXC B₂ ω₂)
    (xs : V → ℤ) (hx₁ : xs ∈ B₁) (hx₂ : xs ∈ B₂) :
    ((∀ x ∈ B₁, x ∈ B₂ → ω₁ x + ω₂ x ≤ ω₁ xs + ω₂ xs) ↔
      ∃ p : V → ℝ, (∀ x ∈ B₁, perturb ω₁ (-p) x ≤ perturb ω₁ (-p) xs) ∧
        (∀ x ∈ B₂, perturb ω₂ p x ≤ perturb ω₂ p xs)) ∧
    ((∀ x ∈ B₁, ∃ k : ℤ, ω₁ x = k) → (∀ x ∈ B₂, ∃ k : ℤ, ω₂ x = k) →
      (∀ x ∈ B₁, x ∈ B₂ → ω₁ x + ω₂ x ≤ ω₁ xs + ω₂ xs) →
      ∃ p : V → ℤ, (∀ x ∈ B₁, perturb ω₁ (-toReal p) x ≤ perturb ω₁ (-toReal p) xs) ∧
        (∀ x ∈ B₂, perturb ω₂ (toReal p) x ≤ perturb ω₂ (toReal p) xs)) := by sorry

end SteinitzExchange.Duality
