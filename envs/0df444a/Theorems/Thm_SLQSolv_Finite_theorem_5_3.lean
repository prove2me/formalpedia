-- Prove2me | Theorems.Thm_SLQSolv_Finite_theorem_5_3
-- name    : SLQSolv.Finite.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:50.097045+00:00
-- url     : https://prove2.me/theorems/9ca7b1f0-c28a-4556-bf9a-20292c9db357
-- title:
--   Theorem 5.3, p. 2295 — (SLQ)⁰ is finite iff {P_ε(0)} is bounded below; then P_ε → P, V⁰ = ⟨Px, x⟩, R + DᵀPD ⩾ 0, N ⩽ P ⩽ M₀
-- statement:
--   Let (H1)–(H2) hold, and assume (5.6): $J^0(0,0;u)\ge0$ for every $u\in\mathcal U[0,T]$. For every $\varepsilon>0$ let $P_\varepsilon$ be the strongly regular solution of the regularized Riccati equation (5.7), i.e. the Riccati equation (4.6) with $R$ replaced by $R+\varepsilon I$:
--
--   $$
--   \dot P_\varepsilon+P_\varepsilon A+A^\top P_\varepsilon+C^\top P_\varepsilon C+Q-(P_\varepsilon B+C^\top P_\varepsilon D+S^\top)(R+\varepsilon I+D^\top P_\varepsilon D)^{-1}(B^\top P_\varepsilon+D^\top P_\varepsilon C+S)=0,\qquad P_\varepsilon(T)=G.
--   $$
--
--   Let $M_0$ be the solution of the Lyapunov equation (3.2), $\Phi_A$ the solution of $\dot\Phi_A=A\Phi_A$, $\Phi_A(0)=I$, and $N(t)=[\Phi_A(t)^\top]^{-1}\{P(0)-\int_0^t\Phi_A^\top(C^\top M_0C+Q)\Phi_A\,ds\}\Phi_A(t)^{-1}$. Then:
--
--   1. Problem (SLQ)$^0$ is finite if and only if $\{P_\varepsilon(0)\}_{\varepsilon>0}$ is bounded from below: there is $\beta\in\mathbb R$ with $P_\varepsilon(0)\ge\beta I$ for all $\varepsilon>0$.
--   2. In this case the limit $P(t)=\lim_{\varepsilon\to0}P_\varepsilon(t)$ exists for every $t\in[0,T]$ (5.9), it represents the value function,
--
--   $$
--   V^0(t,x)=\langle P(t)x,x\rangle\qquad\forall (t,x)\in[0,T]\times\mathbb R^n,
--   $$
--
--   and moreover (5.10) $R+D^\top PD\ge0$ a.e. on $[0,T]$ and (5.11) $N(t)\le P(t)\le M_0(t)$ for all $t\in[0,T]$.
--   3. In particular, if Problem (SLQ)$^0$ is finite at $t=0$, then it is finite.
--
--   The theorem characterizes finiteness of the homogeneous problem, which convexity alone does not give (Example 5.2), by the regularized Riccati solutions, and it identifies the quadratic form of the value function as their monotone limit.
--
--   **Formalization Note** "Bounded from below" is the scalar form $P_\varepsilon(0)\ge\beta I$ with one $\beta$ for all $\varepsilon$, the form the proof uses (p. 2296); any matrix lower bound $K$ yields $\beta=\lambda_{\min}(K)$. The limit is the right limit $\varepsilon\downarrow0$ (`𝓝[>] 0`), since $P_\varepsilon$ is defined for $\varepsilon>0$ only. $P_\varepsilon$, $M_0$ and $\Phi_A$ enter as functions pinned by their defining equations; each is unique (strongly regular solutions by Theorem 4.5, the others by linear ODE uniqueness). The pseudoinverse in the encoded Riccati equation equals the printed inverse on a strongly regular solution. $\Phi_A(t)$ is invertible, so `⁻¹` is the true inverse. Matrix inequalities are Loewner inequalities, written `PosSemidef` of the difference. Finiteness of Problem (SLQ)$^0$ quantifies over $t\in[0,T]$, as in Definition 2.1.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Theorem 5.3, p. 2295 (with (5.6), p. 2294; (5.7), p. 2295; (3.2), p. 2281; (5.1), p. 2292)

import Mathlib
import Definitions.Def_SLQSolv_Finite_Comparison

open MeasureTheory Filter Topology Set
open scoped NNReal Matrix

namespace SLQSolv.Finite

theorem theorem_5_3 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d) (h56 : IsNonnegJ0 Bs d 0)
    (Pε : ℝ → ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hPε : ∀ ε > 0, IsStronglyRegular (d.addR ε) (Pε ε))
    (M0 : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hM0 : IsLyapunovSol d 0 M0)
    (ΦA : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hΦ : IsFundSolA d ΦA) :
    (IsFinite Bs d.hom ↔ ∃ β : ℝ, ∀ ε > 0, (Pε ε 0 - β • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) ∧
    (IsFinite Bs d.hom → ∃ P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ,
      (∀ t ≤ d.T, Tendsto (fun ε => Pε ε t) (𝓝[>] 0) (𝓝 (P t))) ∧
      (∀ t ≤ d.T, ∀ x, V0 Bs d t x = (((P t *ᵥ x) ⬝ᵥ x : ℝ) : EReal)) ∧
      (∀ᵐ s ∂(volume.restrict (Icc (0:ℝ) d.T)), (sigmaR d P s.toNNReal).PosSemidef) ∧
      (∀ t ≤ d.T, (P t - nMat d M0 ΦA P t).PosSemidef ∧ (M0 t - P t).PosSemidef)) ∧
    (IsFiniteAtTime Bs d.hom 0 → IsFinite Bs d.hom) := by sorry

end SLQSolv.Finite
