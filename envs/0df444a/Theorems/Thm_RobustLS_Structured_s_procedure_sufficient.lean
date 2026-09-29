-- Prove2me | Theorems.Thm_RobustLS_Structured_s_procedure_sufficient
-- name    : RobustLS.Structured.s_procedure_sufficient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:33:41.12298+00:00
-- url     : https://prove2.me/theorems/20cebb06-895b-4bd6-ba9a-1126d1c086c3
-- title:
--   Lemma 2.1 (S-procedure) — sufficiency of the multiplier condition, every $p$
-- statement:
--   Let $F_0,\dots,F_p$ be quadratic functions of $\zeta \in \mathbb{R}^m$,
--
--   $$
--   F_i(\zeta) = \zeta^T T_i \zeta + 2u_i^T\zeta + v_i, \qquad i = 0,\dots,p,
--   $$
--
--   with $T_i = T_i^T$. If there exist $\tau_1 \ge 0, \dots, \tau_p \ge 0$ such that
--
--   $$
--   \begin{bmatrix} T_0 & u_0 \\ u_0^T & v_0 \end{bmatrix} - \sum_{i=1}^p \tau_i \begin{bmatrix} T_i & u_i \\ u_i^T & v_i \end{bmatrix} \succeq 0,
--   $$
--
--   then $F_0(\zeta) \ge 0$ for every $\zeta$ such that $F_i(\zeta) \ge 0$ for all $i = 1,\dots,p$.
--
--   This is the "if" half of the S-procedure: a linear matrix inequality in the multipliers certifies that one quadratic inequality is implied by several others. The paper uses it, together with its converse for one constraint, to turn the worst-case residual computation into a semidefinite program.
--
--   **Formalization Note** The functions $F_1,\dots,F_p$ are indexed by `Fin p` (index shifted by one). The block matrices are indexed by `Fin m ⊕ Unit`, the $\zeta$ block first, as printed. The platform theorem `ConvexOptimization.s_procedure` (a reference item of this mission) is the $p=1$ equivalence in the opposite sign convention ($\le 0$ constraints, scalar block last).
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1038, §2.2, Lemma 2.1 (first assertion)

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **Lemma 2.1 (S-procedure), sufficiency, every p** — El Ghaoui & Lebret, Robust Solutions to
Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4) (1997), §2.2,
p. 1038 (PDF p. 4). Let `Fᵢ(ζ) = ζᵀTᵢζ + 2uᵢᵀζ + vᵢ` (`i = 0, …, p`) with `Tᵢ = Tᵢᵀ`. If there
exist `τ₁, …, τ_p ≥ 0` with `[T₀ u₀; u₀ᵀ v₀] − ∑ τᵢ [Tᵢ uᵢ; uᵢᵀ vᵢ] ⪰ 0`, then `F₀(ζ) ≥ 0` for
every `ζ` with `Fᵢ(ζ) ≥ 0` for all `i = 1, …, p`. The family `F₁, …, F_p` is indexed by
`Fin p` (`T i` is the paper's `T_{i+1}`). -/
theorem s_procedure_sufficient {m p : ℕ} (T0 : Matrix (Fin m) (Fin m) ℝ) (u0 : Fin m → ℝ)
    (v0 : ℝ) (T : Fin p → Matrix (Fin m) (Fin m) ℝ) (u : Fin p → Fin m → ℝ) (v : Fin p → ℝ)
    (hT0 : T0ᵀ = T0) (hT : ∀ i, (T i)ᵀ = T i)
    (hτ : ∃ τ : Fin p → ℝ, (∀ i, 0 ≤ τ i) ∧
      (quadBlockMat T0 u0 v0 - ∑ i, τ i • quadBlockMat (T i) (u i) (v i)).PosSemidef) :
    ∀ ζ : Fin m → ℝ, (∀ i, 0 ≤ quadFn (T i) (u i) (v i) ζ) → 0 ≤ quadFn T0 u0 v0 ζ := by sorry

end RobustLS.Structured
