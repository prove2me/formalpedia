-- Prove2me | Theorems.Thm_TimeInconsLQ_Deterministic_theorem_4_2
-- name    : TimeInconsLQ.Deterministic.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:25:07.118984+00:00
-- url     : https://prove2.me/theorems/3e337744-6f26-49be-be9f-01f0c08ae0f8
-- title:
--   Theorem 4.2 — standard case R ⪰ δI: (4.10) and (4.9) have unique positive solution pairs
-- statement:
--   Consider the scalar-state problem with deterministic coefficients of §4 under the standing assumptions, with control dimension $l$ and $\Gamma^{(1)}_s=\mu_1e^{\int_s^TA_r\,dr}$.
--
--   **Theorem 4.2 (standard case).** Assume that $R-\delta I\succeq0$ on $[0,T]$ for some $\delta>0$ and $G\ge h>0$. Suppose
--   $$\frac{QD'D+|C|^2R}{l}+\Gamma^{(1)}\mathcal S(D'CB')\succeq0\quad\text{on }[0,T],$$
--   and either (i) there is a constant $\lambda\ge0$ with $B=\lambda D'C$ on $[0,T]$, or (ii) $D'D-\delta I\succeq0$ on $[0,T]$ for some $\delta>0$. Then (4.10) and (4.9) each admit a positive solution pair on $[0,T]$, and it is unique: any two positive solution pairs agree on $[0,T]$.
--
--   This is the existence and uniqueness result for the coupled Riccati system that yields the equilibrium feedback when the control weight $R$ is uniformly positive definite.
--
--   **Formalization Note.** Solutions are in integral form on $[0,T]$ (the coefficients are only bounded measurable). $\mathcal S(M)=\frac12(M+M')$; the two constants $\delta$ are independent; all conditions hold for every $s\in[0,T]$.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 10, Theorem 4.2

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Deterministic_Model
import Definitions.Def_TimeInconsLQ_Deterministic_Riccati

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace TimeInconsLQ.Deterministic

/-- Theorem 4.2 (p. 10, standard case): if `R − δI ⪰ 0` for some `δ > 0`, `G ≥ h > 0`,
`(QD′D + |C|²R)/l + Γ⁽¹⁾S(D′CB′) ⪰ 0`, and either (i) `B = λD′C` for a constant `λ ≥ 0` or
(ii) `D′D − δI ⪰ 0` for some `δ > 0`, then (4.10) and (4.9) each admit a positive solution
pair, unique on `[0, T]`. -/
theorem theorem_4_2 {l d : ℕ} (c : Coeffs l d) (T : ℝ≥0) (hT : 0 < T)
    (hc : CoeffsStanding c T) (hR : StdCond c T) (hGh : c.h ≤ c.G) (hh : 0 < c.h)
    (hH : HCond c T) (hcase : ColinCond c T ∨ DNondeg c T) :
    HasUniqueSolOn T (IsPosSol410 c T) ∧ HasUniqueSolOn T (IsPosSol49 c T) := by sorry

end TimeInconsLQ.Deterministic
