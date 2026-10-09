-- Prove2me | Theorems.Thm_SLQSolv_UnifConvex_lemma_2_2
-- name    : SLQSolv.UnifConvex.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:53.71387+00:00
-- url     : https://prove2.me/theorems/8fdebf8e-c1a9-48e6-b09e-68ddb434136e
-- title:
--   Lemma 2.2, p. 2279 — the cost J⁰ along a feedback ΘX + u, through the Lyapunov solution P
-- statement:
--   Assume (H1)–(H2). Let $\Theta\in L^2(0,T;\mathbb R^{m\times n})$ and let $P\in C([0,T];\mathbb S^n)$ solve the Lyapunov equation
--
--   $$\dot P+P(A+B\Theta)+(A+B\Theta)^\top P+(C+D\Theta)^\top P(C+D\Theta)+\Theta^\top R\Theta+S^\top\Theta+\Theta^\top S+Q=0,\quad P(T)=G.\qquad(2.5)$$
--
--   Let $(t,x)\in[0,T)\times\mathbb R^n$ and $u\in\mathcal U[t,T]$, and let $X$ solve $dX=[(A+B\Theta)X+Bu]ds+[(C+D\Theta)X+Du]dW$ on $[t,T]$, $X(t)=x$. Then
--
--   $$J^0(t,x;\Theta X+u)=\langle P(t)x,x\rangle+\mathbb E\int_t^T\Big\{\langle(R+D^\top PD)u,u\rangle+2\big\langle[B^\top P+D^\top PC+S+(R+D^\top PD)\Theta]X,u\big\rangle\Big\}ds.$$
--
--   The identity expresses the homogeneous cost of any affine feedback through a deterministic matrix ODE; it is the basic computation behind Proposition 4.4.
--
--   **Formalization Note** The process $X$, introduced in the paper's proof, is taken as a hypothesis: a solution of the homogeneous closed-loop system from $(t,x)$ with control $\Theta X+u$. The Lyapunov equation is in integral form on $[0,T]$.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Lemma 2.2, p. 2279

import Mathlib
import Definitions.Def_SLQSolv_UnifConvex_Riccati

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.UnifConvex

/-- Lemma 2.2, p. 2279. If `P` solves the Lyapunov equation (2.5) of a feedback
`Θ ∈ L²(0, T; ℝ^{m×n})`, then for every `(t, x) ∈ [0, T) × ℝⁿ` and `u ∈ 𝒰[t, T]`, with `X` the
solution of the homogeneous closed-loop system `dX = [(A + BΘ)X + Bu]ds + [(C + DΘ)X + Du]dW`,
`X(t) = x`,
`J⁰(t, x; ΘX + u) = ⟨P(t)x, x⟩ + E∫ₜᵀ {⟨(R + DᵀPD)u, u⟩ + 2⟨[BᵀP + DᵀPC + S + (R + DᵀPD)Θ]X, u⟩} ds`. -/
theorem lemma_2_2 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d)
    (Θ : ℝ≥0 → Matrix (Fin m) (Fin n) ℝ) (hΘ : MatLpOn 2 0 d.T Θ)
    (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hP : IsLyapunovSol d Θ P)
    (t : ℝ≥0) (ht : t < d.T) (x : Fin n → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) (hu : Adm Bs d t u)
    (X : ℝ≥0 → Ω → Fin n → ℝ) (hX : IsClosedLoopState Bs d.hom t Θ u x X) :
    J0 Bs d t x (fun s ω => Θ s *ᵥ X s ω + u s ω) =
      (P t *ᵥ x) ⬝ᵥ x +
        ∫ ω, ∫ s in Icc (t : ℝ) d.T,
          ((sigmaR d P s.toNNReal *ᵥ u s.toNNReal ω) ⬝ᵥ u s.toNNReal ω
            + 2 * (((gainK d P s.toNNReal + sigmaR d P s.toNNReal * Θ s.toNNReal)
                *ᵥ X s.toNNReal ω) ⬝ᵥ u s.toNNReal ω)) ∂volume ∂Bs.P := by sorry

end SLQSolv.UnifConvex
