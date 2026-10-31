-- Prove2me | Theorems.Thm_RobustToDynamics_step2_support_function
-- name    : RobustToDynamics.step2_support_function
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:13.756337+00:00
-- url     : https://prove2.me/theorems/663fe182-54bb-4009-92a3-a9a34f82ce08
-- title:
--   Step 2 — $\max\{a^Tx : x^TMx\le1\}=\sqrt{a^TM^{-1}a}$, attained
-- statement:
--   Let $M$ be a real symmetric positive definite $n\times n$ matrix and $a\in\mathbb R^n$. Then the maximum
--   $$
--   \eta=\max_{x\in\mathbb R^n}\{a^Tx : x^TMx\le1\}
--   $$
--   is attained and equals $\sqrt{a^TM^{-1}a}$.
--
--   Applied to the rows $a_i$ of $A$, this is the closed form of $\eta_i$ used to compute $\alpha_1$ in (2.15).
--
--   Differences from the source:
--   - generalization: a = a_i, a row of A; M the Lyapunov solution → any a ∈ ℝⁿ; any M ≻ 0; reason: the source's instance is a special case
--   - encoding: η_i := max{…} → IsGreatest of the image of E(1) under x ↦ aᵀx; reason: a maximum is a value that is attained and is an upper bound
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 2, pp.14–15

import Mathlib
import Definitions.Def_RobustToDynamics_ellipsoid

open Matrix

namespace RobustToDynamics

/-- **Step 2: the closed form `ηᵢ = √(aᵢᵀM⁻¹aᵢ)`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 2, pp.14–15: "ηi := max_{x∈Rn} {aTi x : xT Mx ≤ 1}. The optimal value here can be computed in
closed form: ηi = √(aTi M−1 ai). Note that M−1 exists as M ≻ 0."

For `M ≻ 0` and every `a ∈ ℝⁿ`, the maximum of `aᵀx` over `{x | xᵀMx ≤ 1}` is attained and equals
`√(aᵀM⁻¹a)`.

**Formalization Note.** "max" is `IsGreatest` of the image set: the value is attained and is an
upper bound. `a` is any real vector (the paper applies it to the rows `aᵢ` of `A`). `M⁻¹` is
`Matrix.inv`, the inverse since `M ≻ 0`. -/
theorem step2_support_function {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (a : Fin n → ℝ) :
    IsGreatest ((fun x => a ⬝ᵥ x) '' ellipsoid M 1) (Real.sqrt (a ⬝ᵥ (M⁻¹ *ᵥ a))) := by sorry

end RobustToDynamics
