-- Prove2me | Theorems.Thm_PrimalDualLDR_FixedRecourse_proposition_1
-- name    : PrimalDualLDR.FixedRecourse.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:45.648817+00:00
-- url     : https://prove2.me/theorems/842f338a-aabb-4935-ac4b-0c9684523c24
-- title:
--   Proposition 1 — $z^\top\xi\ge0$ on $\Xi$ iff some $\lambda\ge0$ has $W^\top\lambda=z$, $h^\top\lambda\ge0$
-- statement:
--   Let $W \in \mathbb R^{l\times k}$ and $h \in \mathbb R^l$, and assume that the polyhedron $\Xi = \{\xi \in \mathbb R^k : W\xi \ge h\}$ is nonempty. Then for every $z \in \mathbb R^k$ the following statements are equivalent:
--
--   1. $z^\top\xi \ge 0$ for all $\xi \in \Xi$;
--   2. there is $\lambda \in \mathbb R^l$ with
--   $$\lambda \ge 0,\qquad W^\top\lambda = z,\qquad h^\top\lambda \ge 0.$$
--
--   This is the robust counterpart of a linear inequality over a polyhedral uncertainty set: a semi-infinite constraint indexed by $\xi \in \Xi$ is replaced by finitely many linear constraints in an auxiliary vector $\lambda$. Applied to each row of $S$ it turns $\mathcal{SP}^u$ into the linear program (2.3), and it is also used to identify the cone $\mathcal K$ in Proposition 3.
--
--   **Formalization Note** The statement is made for any $W, h$ whose polyhedron is nonempty, not only for the support of the §2 setting: nonemptiness is the only property of $\Xi$ the proposition uses (strong LP duality for a feasible primal).
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 5, Proposition 1

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.FixedRecourse

/-- Proposition 1 (p. 5): for a nonempty polyhedron `Ξ = {ξ : Wξ ≥ h}` and any `z ∈ ℝ^k`,
`zᵀξ ≥ 0` for all `ξ ∈ Ξ` iff there is `λ ∈ ℝ^l` with `λ ≥ 0`, `Wᵀλ = z` and `hᵀλ ≥ 0`. -/
theorem proposition_1 {k l : ℕ} (W : Matrix (Fin l) (Fin k) ℝ) (h : Fin l → ℝ)
    (hne : (polyhedron W h).Nonempty) (z : Fin k → ℝ) :
    (∀ ξ ∈ polyhedron W h, 0 ≤ z ⬝ᵥ ξ) ↔
      ∃ lam : Fin l → ℝ, (∀ i, 0 ≤ lam i) ∧ Wᵀ.mulVec lam = z ∧ 0 ≤ h ⬝ᵥ lam := by sorry

end PrimalDualLDR.FixedRecourse
