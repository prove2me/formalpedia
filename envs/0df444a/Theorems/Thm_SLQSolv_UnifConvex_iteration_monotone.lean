-- Prove2me | Theorems.Thm_SLQSolv_UnifConvex_iteration_monotone
-- name    : SLQSolv.UnifConvex.iteration_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:19:31.340314+00:00
-- url     : https://prove2.me/theorems/94ec9092-0084-44be-b19b-01733df99745
-- title:
--   Proof of Theorem 4.5, (4.20) and p. 2289 — the Riccati iterates satisfy R + DᵀPᵢ₊₁D ≥ λI and P₁ ≥ Pᵢ ≥ Pᵢ₊₁ ≥ αI
-- statement:
--   Assume (H1)–(H2), (4.2) with constant $\lambda>0$ and (4.1) with constant $\alpha$. Let $P_0$ solve
--
--   $$\dot P_0+P_0A+A^\top P_0+C^\top P_0C+Q=0,\quad P_0(T)=G,\qquad(4.18)$$
--
--   and inductively, for $i=0,1,2,\dots$, set $\Theta_i=-(R+D^\top P_iD)^{-1}(B^\top P_i+D^\top P_iC+S)$, $A_i=A+B\Theta_i$, $C_i=C+D\Theta_i$ (4.19), and let $P_{i+1}$ solve
--
--   $$\dot P_{i+1}+P_{i+1}A_i+A_i^\top P_{i+1}+C_i^\top P_{i+1}C_i+\Theta_i^\top R\Theta_i+S^\top\Theta_i+\Theta_i^\top S+Q=0,\quad P_{i+1}(T)=G.$$
--
--   Then for every $i\ge0$
--
--   $$R+D^\top P_{i+1}D\ \ge\ \lambda I\ \text{ a.e. on }[0,T],\qquad P_{i+1}(s)\ge\alpha I\ \ \forall s\in[0,T],\qquad(4.20)$$
--
--   and
--
--   $$P_1(s)\ \ge\ P_i(s)\ \ge\ P_{i+1}(s)\ \ge\ \alpha I\qquad\forall s\in[0,T],\ \forall i\ge1.$$
--
--   Monotonicity and the lower bound make the sequence uniformly bounded, the first step towards its uniform convergence.
--
--   **Formalization Note** The sequence is given through hypotheses: $P_0$ solves the Lyapunov equation with $\Theta=0$ and $P_{i+1}$ solves the Lyapunov equation of $\Theta_i$. Lyapunov solutions are unique, so this is the paper's sequence. $\Theta_i$ uses the matrix inverse, as printed; its invertibility is part of (4.20).
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §4, proof of Theorem 4.5, (4.18)–(4.20) and the display after (4.23), pp. 2288–2289

import Mathlib
import Definitions.Def_SLQSolv_UnifConvex_Iteration

open MeasureTheory Set Filter Topology
open scoped NNReal Matrix

namespace SLQSolv.UnifConvex

/-- §4, proof of Theorem 4.5, (4.20) and the display after (4.23), p. 2289. Under (4.2) (constant
`λ`) and (4.1) (constant `α`), let `P₀` solve (4.18) and `P_{i+1}` solve the Lyapunov equation of
`Θᵢ = −(R + DᵀPᵢD)⁻¹(BᵀPᵢ + DᵀPᵢC + S)` (4.19). Then for every `i ≥ 0`,
`R + DᵀP_{i+1}D ≥ λI` a.e. and `P_{i+1} ≥ αI` on `[0, T]`, and for `i ≥ 1`,
`P₁(s) ≥ Pᵢ(s) ≥ P_{i+1}(s) ≥ αI` for all `s ∈ [0, T]`. -/
theorem iteration_monotone {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω)
    (d : Data Ω n m) (h1 : H1 Bs d) (h2 : H2 Bs d)
    (lam : ℝ) (hlam : 0 < lam) (h42 : ∀ u, Adm Bs d 0 u → lam * sqNorm Bs d 0 u ≤ J0 Bs d 0 0 u)
    (α : ℝ) (h41 : ∀ t ≤ d.T, ∀ x : Fin n → ℝ, ((α * (x ⬝ᵥ x) : ℝ) : EReal) ≤ V0 Bs d t x)
    (Pseq : ℕ → ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (hP0 : IsLyapunovSol d 0 (Pseq 0))
    (hPsucc : ∀ i, IsLyapunovSol d (thetaOf d (Pseq i)) (Pseq (i + 1))) :
    ∀ i : ℕ,
      (∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) d.T)),
          (sigmaR d (Pseq (i + 1)) s.toNNReal - lam • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef) ∧
        (∀ s ≤ d.T, (Pseq (i + 1) s - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) ∧
        (1 ≤ i → ∀ s ≤ d.T,
          (Pseq 1 s - Pseq i s).PosSemidef ∧ (Pseq i s - Pseq (i + 1) s).PosSemidef) := by sorry

end SLQSolv.UnifConvex
