-- Prove2me | Theorems.Thm_SLQSolv_UnifConvex_proposition_4_4
-- name    : SLQSolv.UnifConvex.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:22:07.893171+00:00
-- url     : https://prove2.me/theorems/172f1813-75bf-4aa1-8341-417108884ee1
-- title:
--   Proposition 4.4, p. 2287 — every Lyapunov solution satisfies R + DᵀPD ≥ λI and P ≥ αI
-- statement:
--   Assume (H1)–(H2) and (4.2): $J^0(0,0;u)\ge\lambda\,\mathbb E\int_0^T|u|^2ds$ for all $u\in\mathcal U[0,T]$, with $\lambda>0$. Let $\alpha\in\mathbb R$ be a constant with (4.1): $V^0(t,x)\ge\alpha|x|^2$ for all $(t,x)\in[0,T]\times\mathbb R^n$. Then for every $\Theta\in L^2(0,T;\mathbb R^{m\times n})$ the solution $P\in C([0,T];\mathbb S^n)$ of the Lyapunov equation
--
--   $$\dot P+P(A+B\Theta)+(A+B\Theta)^\top P+(C+D\Theta)^\top P(C+D\Theta)+\Theta^\top R\Theta+S^\top\Theta+\Theta^\top S+Q=0,\quad P(T)=G\qquad(4.15)$$
--
--   satisfies
--
--   $$R(t)+D(t)^\top P(t)D(t)\ \ge\ \lambda I\ \text{ a.e. } t\in[0,T],\qquad P(t)\ \ge\ \alpha I\ \ \forall t\in[0,T].\qquad(4.16)$$
--
--   The constants are the same $\lambda$ of (4.2) and $\alpha$ of (4.1), uniformly in $\Theta$. This is the key estimate that keeps the Riccati iteration well defined and bounded.
--
--   **Formalization Note** $\lambda$ and $\alpha$ are explicit parameters with their hypotheses, not existential constants. Matrix inequalities are positive semidefiniteness of the difference.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Proposition 4.4, p. 2287

import Mathlib
import Definitions.Def_SLQSolv_UnifConvex_Riccati

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.UnifConvex

/-- Proposition 4.4, p. 2287. Under (4.2) with constant `λ > 0` and (4.1) with constant `α`, for
every `Θ ∈ L²(0, T; ℝ^{m×n})` the solution `P` of the Lyapunov equation (4.15) satisfies (4.16):
`R + DᵀPD ≥ λI` a.e. on `[0, T]` and `P(t) ≥ αI` for all `t ∈ [0, T]`. -/
theorem proposition_4_4 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω)
    (d : Data Ω n m) (h1 : H1 Bs d) (h2 : H2 Bs d)
    (lam : ℝ) (hlam : 0 < lam) (h42 : ∀ u, Adm Bs d 0 u → lam * sqNorm Bs d 0 u ≤ J0 Bs d 0 0 u)
    (α : ℝ) (h41 : ∀ t ≤ d.T, ∀ x : Fin n → ℝ, ((α * (x ⬝ᵥ x) : ℝ) : EReal) ≤ V0 Bs d t x)
    (Θ : ℝ≥0 → Matrix (Fin m) (Fin n) ℝ) (hΘ : MatLpOn 2 0 d.T Θ)
    (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hP : IsLyapunovSol d Θ P) :
    (∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) d.T)),
        (sigmaR d P s.toNNReal - lam • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef) ∧
      ∀ t ≤ d.T, (P t - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by sorry

end SLQSolv.UnifConvex
