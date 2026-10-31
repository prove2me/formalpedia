-- Prove2me | Theorems.Thm_RobustToDynamics_step2_inner_ellipsoid
-- name    : RobustToDynamics.step2_inner_ellipsoid
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:25.164683+00:00
-- url     : https://prove2.me/theorems/1252d042-43fe-4a4f-a52f-af9afa9909b0
-- title:
--   (2.15) — with $0\in\operatorname{int}P$: $b_i>0$ on nonzero rows, $\alpha_1>0$ and $E(\alpha_1)\subseteq P$ (corrected: $b_i>0$ only for rows $a_i\neq0$)
-- statement:
--   Let $M$ be a real symmetric positive definite $n\times n$ matrix, $A\in\mathbb R^{m\times n}$ with rows $a_i^T$, $b\in\mathbb R^m$, and suppose the origin lies in the interior of $P=\{x: Ax\le b\}$. Put
--   $$
--   \alpha_1=\min_{i:\ a_i\neq0}\frac{b_i^2}{a_i^TM^{-1}a_i}. \tag{2.15}
--   $$
--   Then
--
--   1. $b_i>0$ for every $i$ with $a_i\neq0$;
--   2. $\alpha_1>0$;
--   3. $E(\alpha_1)=\{x: x^TMx\le\alpha_1\}\subseteq P$.
--
--   $E(\alpha_1)$ is the inner ellipsoid of Step 2: an invariant set inside $P$.
--
--   **Formalization Note** If $A$ has no nonzero row, $\alpha_1=1$ by convention.
--
--   Differences from the source:
--   - reading: α₁ = min over i ∈ {1, …, m} of b_i²/(a_iᵀM⁻¹a_i) → the minimum over the rows with a_i ≠ 0 (α₁ = 1 if there is none); reason: at a zero row the printed quotient has denominator 0 and is undefined; such a row constrains nothing
--   - correction: b_i > 0 for i = 1, …, m as the origin is in the interior of P → b_i > 0 for every i with a_i ≠ 0; reason: counterexample: n = 1, A = (1, −1, 0)ᵀ, b = (1, 1, 0): P = [−1, 1] has the origin in its interior but b₃ = 0
--   - generalization: M the Lyapunov solution; rational data → any M ≻ 0; real data; reason: the source's instance is a special case
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 2, display (2.15), p.15

import Mathlib
import Definitions.Def_RobustToDynamics_polyhedron
import Definitions.Def_RobustToDynamics_ellipsoid
import Definitions.Def_RobustToDynamics_alpha1

open Matrix

namespace RobustToDynamics

/-- **(2.15): the inner ellipsoid `E(α₁) ⊆ P`, with `α₁ > 0`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 2, display (2.15), p.15: "α1 = min {b2i /η2i} = min { b2i / (aTi M−1ai) }. This ensures that
∀i ∈ {1, . . . , m}, ∀x ∈ E(α1), we have aTi x ≤ bi. Hence, E(α1) ⊆ P. Note that α1 > 0 since
M−1 ≻ 0, and bi > 0 for i = 1, . . . , m as the origin is in the interior of P."

Let `M ≻ 0` and let the origin lie in the interior of `P = {x | Ax ≤ b}`. Then `bᵢ > 0` for every
nonzero row `aᵢ`, `α₁ > 0`, and `E(α₁) ⊆ P`.

**Formalization Note.** `α₁` is `alpha1`: the minimum is over the rows with `aᵢ ≠ 0` (at a zero row
the printed quotient is undefined); with no nonzero row it is `1`. The claim `bᵢ > 0` is stated for
nonzero rows only: a zero row with `bᵢ = 0` leaves `P` unchanged and keeps the origin interior. The
data are real (a generalization of rational data). -/
theorem step2_inner_ellipsoid {m n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (h0 : (0 : Fin n → ℝ) ∈ interior (polyhedron A b)) :
    (∀ i, A i ≠ 0 → 0 < b i) ∧ 0 < alpha1 M A b ∧
      ellipsoid M (alpha1 M A b) ⊆ polyhedron A b := by sorry

end RobustToDynamics
