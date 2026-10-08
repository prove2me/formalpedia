-- Prove2me | Theorems.Thm_VanderbeiLP_SelfDual_iterates_bounded_away_from_zero
-- name    : VanderbeiLP.SelfDual.iterates_bounded_away_from_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:53:50.803856+00:00
-- url     : https://prove2.me/theorems/5ab27208-bc70-4cd2-a743-d8ee373cd2b1
-- title:
--   Theorem 22.7 — iterates in $\mathcal N(\beta)$ satisfy $x_j + z_j \ge c_j > 0$
-- statement:
--   Let $n \ge 2$, let $A$ be a real skew-symmetric $n \times n$ matrix, and let $0 \le \beta < 1$. The predictor–corrector algorithm starts from $x^{(0)} = z^{(0)} = e$, so $\rho^{(0)} = \rho(e, e) = Ae + e$, and by Theorem 22.2 each of its iterates satisfies $\rho(x, z) = \mu(x, z)\rho^{(0)}$.
--
--   There exist positive constants $c_1, c_2, \dots, c_n$ such that every $(x, z) \in \mathcal N(\beta)$ with
--   $$\rho(x, z) = \mu(x, z)\,\rho^{(0)}$$
--   satisfies
--   $$x_j + z_j \ge c_j > 0 \qquad \text{for each } j = 1, 2, \dots, n.$$
--
--   The constants depend only on $A$ and $\beta$, not on $(x, z)$. The theorem says that the iterates cannot approach the boundary in a coordinate where both $x_j$ and $z_j$ vanish, which is the main idea behind the strict complementarity of the limit (Theorem 22.6).
--
--   **Formalization Note** The book states the theorem for "$(x, z) \in \mathcal N(\beta)$", and its proof uses $\rho = \mu\rho^{(0)}$, which holds along the algorithm's iterates (p. 331); that relation is therefore a hypothesis. Without it the statement is false in general. The book's proof uses $\beta < 1$ (it divides by $1 - \beta$). The existence of a strictly complementary feasible solution of (22.4), which the book's proof takes from Theorem 10.6, is not assumed.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 332, Theorem 22.7 (PDF p. 338); the relation ρ⁽ᵏ⁾ = μ⁽ᵏ⁾ρ⁽⁰⁾ and the start x⁽⁰⁾ = z⁽⁰⁾ = e on p. 331 (PDF p. 337)

import Mathlib
import Definitions.Def_VanderbeiLP_SelfDual_HomogeneousSelfDual

open Matrix

namespace VanderbeiLP.SelfDual

/-- Theorem 22.7 (Vanderbei, p. 332). Let `A` be skew symmetric (`n ≥ 2`) and `0 ≤ β < 1`.
There exist positive constants `c₁, …, cₙ` (depending on `A` and `β` only) such that every
iterate `(x, z) ∈ N(β)` of the algorithm started at `x⁽⁰⁾ = z⁽⁰⁾ = e` — i.e. every
`(x, z) ∈ N(β)` whose infeasibility satisfies `ρ(x, z) = μ(x, z) ρ⁽⁰⁾` with
`ρ⁽⁰⁾ = ρ(e, e)` — has `xⱼ + zⱼ ≥ cⱼ > 0` for each `j`. -/
theorem iterates_bounded_away_from_zero {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ c : Fin n → ℝ, (∀ j, 0 < c j) ∧
      ∀ x z : Fin n → ℝ, (x, z) ∈ Nbhd β →
        rho A x z = mu x z • rho A (fun _ => 1) (fun _ => 1) →
        ∀ j, c j ≤ x j + z j := by sorry

end VanderbeiLP.SelfDual
