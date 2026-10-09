-- Prove2me | Theorems.Thm_SLQSolv_MinSeq_theorem_6_2
-- name    : SLQSolv.MinSeq.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:04.674681+00:00
-- url     : https://prove2.me/theorems/dc4250e0-dbf1-40af-8b92-9899ff223afc
-- title:
--   Theorem 6.2, p. 2301 — open-loop solvability at (t, x) ⟺ u_ε has a weakly ⟺ strongly convergent subsequence; every such limit is optimal
-- statement:
--   Assume (H1)–(H2) and that $u\mapsto J^0(0,0;u)$ is convex on $\mathcal U[0,T]$. Fix $(t,x)\in[0,T)\times\mathbb R^n$. For every $\varepsilon>0$ let $P_\varepsilon$ be a strongly regular solution of the Riccati equation (5.7), i.e. (4.6) with $R$ replaced by $R+\varepsilon I$; let $(\eta_\varepsilon,\zeta_\varepsilon)$ be the adapted solution of the backward equation (4.11) for the same data and $P_\varepsilon$; put $\Theta_\varepsilon=-(R+\varepsilon I+D^\top P_\varepsilon D)^{-1}(B^\top P_\varepsilon+D^\top P_\varepsilon C+S)$ and $v_\varepsilon=-(R+\varepsilon I+D^\top P_\varepsilon D)^{-1}(B^\top\eta_\varepsilon+D^\top\zeta_\varepsilon+D^\top P_\varepsilon\sigma+\rho)$ as in (6.1); let $X_\varepsilon$ solve the closed-loop system $dX_\varepsilon=[(A+B\Theta_\varepsilon)X_\varepsilon+Bv_\varepsilon+b]ds+[(C+D\Theta_\varepsilon)X_\varepsilon+Dv_\varepsilon+\sigma]dW$ on $[t,T]$, $X_\varepsilon(t)=x$; and set $u_\varepsilon=\Theta_\varepsilon X_\varepsilon+v_\varepsilon$ as in (6.2). Then the following are equivalent:
--
--   1. Problem (SLQ) is open-loop solvable at $(t,x)$;
--   2. there are $\varepsilon_k>0$ with $\varepsilon_k\to0$ and $u^*\in\mathcal U[t,T]$ such that $u_{\varepsilon_k}\to u^*$ weakly in $\mathcal U[t,T]=L^2_{\mathbb F}(t,T;\mathbb R^m)$;
--   3. there are $\varepsilon_k>0$ with $\varepsilon_k\to0$ and $u^*\in\mathcal U[t,T]$ such that
--
--   $$
--   \lim_{k\to\infty}\mathbb E\int_t^T|u_{\varepsilon_k}(s)-u^*(s)|^2ds=0.
--   $$
--
--   Moreover, whenever $\varepsilon_k>0$, $\varepsilon_k\to0$ and $u_{\varepsilon_k}$ converges weakly or strongly to some $u^*\in\mathcal U[t,T]$, the limit $u^*$ is an open-loop optimal control of Problem (SLQ) at $(t,x)$.
--
--   The theorem characterizes open-loop solvability without uniform convexity, through a sequence computed from Riccati equations, and identifies the optimal control as the limit of the regularized feedback controls.
--
--   **Formalization Note** "A subsequence of $\{u_\varepsilon\}_{\varepsilon>0}$" is a sequence $\varepsilon_k>0$ tending to $0$. The backward equation is (4.11) of p. 2285 for the data with $R+\varepsilon I$, whose $\rho$-term is $-(P_\varepsilon B+C^\top P_\varepsilon D+S^\top)(R+\varepsilon I+D^\top P_\varepsilon D)^{-1}\rho=+\Theta_\varepsilon^\top\rho$. Theorem 6.1 on p. 2300 prints $-\Theta_\varepsilon^\top\rho$; its proof invokes Corollary 4.7 (p. 2291), which uses (4.11), so the sign of (4.11) is the one formalized. A scalar example confirms (4.11). The families $P_\varepsilon,(\eta_\varepsilon,\zeta_\varepsilon),X_\varepsilon$ enter as hypotheses that pin them by their equations for every $\varepsilon>0$ (each is unique: the strongly regular Riccati solution by [23], the BSDE and the SDE by their uniqueness theorems), so $u_\varepsilon$ is the Riccati feedback sequence (6.2), not an arbitrary minimizing sequence. The sequence is written `uEps`. (H1)–(H2) are the standing assumptions; the state, cost, value function and optimality notions are those of the shared `Setting` module.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Theorem 6.2, p. 2301 (with (6.1)–(6.2), p. 2301, and the BSDE of Theorem 6.1, p. 2300)

import Mathlib
import Definitions.Def_SLQSolv_MinSeq_Sequence

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Matrix

namespace SLQSolv.MinSeq

/-- Theorem 6.2, p. 2301: under (H1)–(H2) and convexity of `u ↦ J⁰(0, 0; u)`, for
`(t, x) ∈ [0, T) × ℝⁿ` and the sequence `u_ε` of (6.2), open-loop solvability at `(t, x)` is
equivalent to (ii) a weakly convergent subsequence `u_{ε_k}`, `ε_k → 0⁺`, with limit in `𝒰[t, T]`,
and to (iii) a strongly convergent one; and every such weak or strong limit is an open-loop optimal
control at `(t, x)`. -/
theorem theorem_6_2 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d)
    (hconv : IsConvexJ0 Bs d) (t : ℝ≥0) (ht : t < d.T) (x : Fin n → ℝ)
    (Pε : ℝ → ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ ε > 0, IsStronglyRegular (d.addR ε) (Pε ε))
    (η ζ : ℝ → ℝ≥0 → Ω → Fin n → ℝ)
    (hηζ : ∀ ε > 0, IsAdjointEta Bs (d.addR ε) (Pε ε) (η ε) (ζ ε))
    (X : ℝ → ℝ≥0 → Ω → Fin n → ℝ)
    (hX : ∀ ε > 0, IsClosedLoopState Bs d t (thetaOf (d.addR ε) (Pε ε))
      (vOf (d.addR ε) (Pε ε) (η ε) (ζ ε)) x (X ε)) :
    (OpenLoopSolvableAt Bs d t x ↔ ∃ εs : ℕ → ℝ, (∀ k, 0 < εs k) ∧ Tendsto εs atTop (𝓝 0) ∧
        ∃ u, Adm Bs d t u ∧ WeakConvU Bs d t (fun k => uEps d Pε η ζ X (εs k)) u) ∧
    (OpenLoopSolvableAt Bs d t x ↔ ∃ εs : ℕ → ℝ, (∀ k, 0 < εs k) ∧ Tendsto εs atTop (𝓝 0) ∧
        ∃ u, Adm Bs d t u ∧ StrongConvU Bs d t (fun k => uEps d Pε η ζ X (εs k)) u) ∧
    (∀ εs : ℕ → ℝ, (∀ k, 0 < εs k) → Tendsto εs atTop (𝓝 0) → ∀ u, Adm Bs d t u →
        (WeakConvU Bs d t (fun k => uEps d Pε η ζ X (εs k)) u ∨
          StrongConvU Bs d t (fun k => uEps d Pε η ζ X (εs k)) u) →
        IsOpenLoopOptimal Bs d t x u) := by sorry

end SLQSolv.MinSeq
