-- Prove2me | Theorems.Thm_RobustLS_Structured_s_procedure_lossless
-- name    : RobustLS.Structured.s_procedure_lossless
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:34:17.177825+00:00
-- url     : https://prove2.me/theorems/562e06b5-fdec-43d1-93ad-9cf44e3f913f
-- title:
--   Lemma 2.1 (S-procedure) — the converse for one constraint ($p = 1$)
-- statement:
--   Let $F_0(\zeta) = \zeta^T T_0\zeta + 2u_0^T\zeta + v_0$ and $F_1(\zeta) = \zeta^T T_1\zeta + 2u_1^T\zeta + v_1$ be quadratic functions of $\zeta \in \mathbb{R}^m$ with $T_0 = T_0^T$, $T_1 = T_1^T$, and assume there is some $\zeta_0$ with $F_1(\zeta_0) > 0$. If $F_0(\zeta) \ge 0$ for every $\zeta$ such that $F_1(\zeta) \ge 0$, then there exists $\tau_1 \ge 0$ such that
--
--   $$
--   \begin{bmatrix} T_0 & u_0 \\ u_0^T & v_0 \end{bmatrix} - \tau_1 \begin{bmatrix} T_1 & u_1 \\ u_1^T & v_1 \end{bmatrix} \succeq 0 .
--   $$
--
--   This is the lossless direction of the S-procedure: with a single strictly feasible quadratic constraint, the multiplier certificate of the first half of Lemma 2.1 always exists. It is the step that makes the SDP characterization of the structured worst-case residual exact rather than a bound.
--
--   **Formalization Note** Block matrices are indexed by `Fin m ⊕ Unit`, the $\zeta$ block first, as printed. This is the same theorem as the platform's `ConvexOptimization.s_procedure` after replacing $F_i$ by $-F_i$ and permuting the block index; that statement is included as a reference item.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1038, §2.2, Lemma 2.1 (last sentence: the converse for p = 1)

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **Lemma 2.1 (S-procedure), converse for p = 1** — El Ghaoui & Lebret (1997), §2.2,
p. 1038 (PDF p. 4). Let `F₀(ζ) = ζᵀT₀ζ + 2u₀ᵀζ + v₀` and `F₁(ζ) = ζᵀT₁ζ + 2u₁ᵀζ + v₁`, with
`T₀ = T₀ᵀ`, `T₁ = T₁ᵀ`, and suppose some `ζ₀` has `F₁(ζ₀) > 0`. If `F₀(ζ) ≥ 0` for every
`ζ` with `F₁(ζ) ≥ 0`, then there is `τ₁ ≥ 0` with `[T₀ u₀; u₀ᵀ v₀] − τ₁ [T₁ u₁; u₁ᵀ v₁] ⪰ 0`. -/
theorem s_procedure_lossless {m : ℕ} (T0 : Matrix (Fin m) (Fin m) ℝ) (u0 : Fin m → ℝ)
    (v0 : ℝ) (T1 : Matrix (Fin m) (Fin m) ℝ) (u1 : Fin m → ℝ) (v1 : ℝ)
    (hT0 : T0ᵀ = T0) (hT1 : T1ᵀ = T1)
    (hslater : ∃ ζ0 : Fin m → ℝ, 0 < quadFn T1 u1 v1 ζ0)
    (himp : ∀ ζ : Fin m → ℝ, 0 ≤ quadFn T1 u1 v1 ζ → 0 ≤ quadFn T0 u0 v0 ζ) :
    ∃ τ1 : ℝ, 0 ≤ τ1 ∧ (quadBlockMat T0 u0 v0 - τ1 • quadBlockMat T1 u1 v1).PosSemidef := by sorry

end RobustLS.Structured
