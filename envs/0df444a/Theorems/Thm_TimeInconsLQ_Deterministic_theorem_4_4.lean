-- Prove2me | Theorems.Thm_TimeInconsLQ_Deterministic_theorem_4_4
-- name    : TimeInconsLQ.Deterministic.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:25:23.872115+00:00
-- url     : https://prove2.me/theorems/4e65771d-4592-4431-8cc3-5a189957ce66
-- title:
--   Theorem 4.4 — under G ≥ h > 0 and cases (i)–(iii), (4.9) has a unique positive solution and the linear feedback (4.4) is an equilibrium
-- statement:
--   Consider the time-inconsistent LQ problem with scalar state ($n=1$) and deterministic coefficients of §4, under the standing assumptions, with control dimension $l$ and $\Gamma^{(1)}_s=\mu_1e^{\int_s^TA_r\,dr}$.
--
--   **Theorem 4.4.** Suppose $G\ge h>0$ and one of the following holds on $[0,T]$:
--   1. $R-\delta I\succeq0$ for some $\delta>0$, $\frac{QD'D+|C|^2R}{l}+\Gamma^{(1)}\mathcal S(D'CB')\succeq0$, and $B=\lambda D'C$ for some $\lambda\ge0$;
--   2. $R-\delta I\succeq0$ for some $\delta>0$, $\frac{QD'D+|C|^2R}{l}+\Gamma^{(1)}\mathcal S(D'CB')\succeq0$, and $D'D-\delta I\succeq0$ for some $\delta>0$;
--   3. $R\equiv0$, $D'D-\delta I\succeq0$ for some $\delta>0$, $Q+\Gamma^{(1)}B'(D'D)^{-1}(B+D'C)\ge0$ and $Q+\Gamma^{(1)}B'(D'D)^{-1}D'C\ge0$.
--
--   Then the coupled Riccati system (4.9) admits a positive solution pair $(M,N)$ on $[0,T]$, unique on $[0,T]$. Moreover, let $\Phi$ solve the linear ODE (4.8) and set
--   $$u^*_s=\alpha_sX^*_s+\beta_s,\qquad\alpha_s=-(R_s+M_sD_s'D_s)^{-1}\big[(M_s-N_s-\Gamma^{(1)}_s)B_s+M_sD_s'C_s\big],\quad\beta_s=-(R_s+M_sD_s'D_s)^{-1}(\Phi_sB_s+M_sD_s'\sigma_s).\tag{4.4}$$
--   On every probability space carrying a standard $d$-dimensional Brownian motion and for every initial state, the closed-loop state equation has a solution $X^*$, and for every such $X^*$ the control $u^*$ is an equilibrium control in the sense of Definition 2.1.
--
--   This is the main result of §4: for deterministic coefficients the open-loop equilibrium of the time-inconsistent LQ problem is a linear feedback of the current state, computed from a deterministic system of ODEs.
--
--   **Formalization Note.** Riccati systems are solved in integral form on $[0,T]$ and uniqueness means agreement on $[0,T]$. "Let $\Phi$ be a solution of (4.8)" is read as: for every solution. "$u^*$ given by (4.4) is an equilibrium" is read as: a closed-loop state exists, and for every closed-loop state the feedback control satisfies Definition 2.1 (with $\liminf$ along sequences, as in the `Model` module). The paper's Theorem 4.3 proves existence only in case (iii); Theorem 4.4 claims uniqueness in all three cases, and so does this statement.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 14, Theorem 4.4

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Deterministic_Model
import Definitions.Def_TimeInconsLQ_Deterministic_Riccati

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace TimeInconsLQ.Deterministic

/-- Theorem 4.4 (p. 14). Suppose `G ≥ h > 0` and one of the cases (i), (ii), (iii) holds. Then
(4.9) admits a positive solution pair `(M, N)`, unique on `[0, T]`. Moreover, for every positive
solution pair `(M, N)` and every solution `Φ` of (4.8), on every probability space carrying a
standard `d`-dimensional Brownian motion and for every initial state, the closed-loop equation
of the feedback (4.4) `u*_s = α_sX*_s + β_s` has a solution, and for every such solution `X*`
the control `u*` is an equilibrium (Definition 2.1). -/
theorem theorem_4_4 {Ω : Type*} [MeasurableSpace Ω] {l d : ℕ} (c : Coeffs l d) (T : ℝ≥0)
    (hT : 0 < T) (hc : CoeffsStanding c T) (hGh : c.h ≤ c.G) (hh : 0 < c.h)
    (hcase : Case_i c T ∨ Case_ii c T ∨ Case_iii c T) :
    HasUniqueSolOn T (IsPosSol49 c T) ∧
    ∀ M N Φ : ℝ≥0 → ℝ, IsPosSol49 c T M N → IsSol48 c T M N Φ →
      ∀ (P : Measure Ω), IsProbabilityMeasure P →
      ∀ (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W) (x₀ : Fin 1 → ℝ),
        (∃ X, IsClosedLoop (toData c P W hW T hT x₀)
            (fun s _ => alpha c T M N s) (fun s _ => beta c M Φ s) X) ∧
        ∀ X, IsClosedLoop (toData c P W hW T hT x₀)
            (fun s _ => alpha c T M N s) (fun s _ => beta c M Φ s) X →
          TimeInconsLQ.Sufficient.IsEquilibrium (toData c P W hW T hT x₀)
            (fun s ω => X s ω 0 • alpha c T M N s + beta c M Φ s) := by sorry

end TimeInconsLQ.Deterministic
