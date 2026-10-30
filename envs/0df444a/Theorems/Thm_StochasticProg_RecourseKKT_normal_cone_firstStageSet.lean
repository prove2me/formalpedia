-- Prove2me | Theorems.Thm_StochasticProg_RecourseKKT_normal_cone_firstStageSet
-- name    : StochasticProg.RecourseKKT.normal_cone_firstStageSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:51:26.531211+00:00
-- url     : https://prove2.me/theorems/9ec15f7f-1a49-42fc-aa26-8add64d22146
-- title:
--   Normal cone of $K_1$: $\{\eta\mid\eta^{\mathsf T}(x-x^*)\ge0\ \forall x\in K_1\}=\{A^{\mathsf T}\lambda+\mu\mid\mu\ge0,\ \mu^{\mathsf T}x^*=0\}$
-- statement:
--   Let $K_1 = \{x \in \mathbb R^{n_1} \mid Ax = b,\ x \ge 0\}$ and $x^* \in K_1$. Then
--
--   $$
--   \{\, \eta \mid \eta^{\mathsf T}(x - x^*) \ge 0 \text{ for all } x \in K_1 \,\} = \{\, A^{\mathsf T}\lambda + \mu \mid \lambda \in \mathbb R^{m_1},\ \mu \in \mathbb R^{n_1},\ \mu \ge 0,\ \mu^{\mathsf T} x^* = 0 \,\}.
--   $$
--
--   This identity, a consequence of linear programming duality, turns the abstract optimality condition of a convex function over $K_1$ into the multipliers $\lambda^*, \mu^*$ of the Karush–Kuhn–Tucker condition (1.12).
--
--   Differences from the source:
--   - encoding: λ ∈ ℜ^{m1}, μ ≥ 0, Aᵀλ → lam : Fin m1 → ℝ, 0 ≤ mu componentwise, Aᵀ *ᵥ lam; reason: Lean notation; same instances
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1e, proof of Theorem 9, printed p. 116 (PDF p. 141)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_firstStageSet
open Matrix

namespace StochasticProg.RecourseKKT

/-- **The normal cone of `K₁` (proof of Theorem 9).**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1e, proof of Theorem 9, printed p. 116 (PDF p. 141): "We can write the set,
{η | ηᵀ(x − x*) ≥ 0 for all x ∈ K₁}, as {η | η = Aᵀλ + μ , for some μ ≥ 0 , μᵀx* = 0}."

For `x* ∈ K₁ = {x | Ax = b, x ≥ 0}`, the vectors `η` with `ηᵀ(x − x*) ≥ 0` for all `x ∈ K₁` are
exactly the vectors `Aᵀλ + μ` with `λ ∈ ℜ^{m1}`, `μ ∈ ℜ^{n1}`, `μ ≥ 0` and `μᵀx* = 0`.

**Formalization Note.** `Aᵀ *ᵥ λ` is the matrix–vector product `Aᵀλ`; `0 ≤ μ` is componentwise. -/
theorem normal_cone_firstStageSet {n1 m1 : ℕ} (A : Matrix (Fin m1) (Fin n1) ℝ)
    (b : Fin m1 → ℝ) (xs : Fin n1 → ℝ) (hxs : xs ∈ firstStageSet A b) :
    {η : Fin n1 → ℝ | ∀ x ∈ firstStageSet A b, 0 ≤ η ⬝ᵥ (x - xs)} =
      {η | ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
        η = Aᵀ *ᵥ lam + mu} := by sorry

end StochasticProg.RecourseKKT
