-- Prove2me | Theorems.Thm_ProdHedgeCVaR_Joint_theorem_2_optimum_binding
-- name    : ProdHedgeCVaR.Joint.theorem_2_optimum_binding
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-29T09:24:37.218532+00:00
-- url     : https://prove2.me/theorems/98505e68-4841-4783-b7aa-ec5cfe38fd0f
-- title:
--   Theorem 2 (ii), p. 20 — if C ≤ C° and (λ*, Q*) solves (53)+(45b), the unique optimal solution of (36) is (pQ* − C, Q*)
-- statement:
--   Throughout, the setting is that of the goal theorem `ProdHedgeCVaR.Joint.theorem_2` (the definitions of `Definitions.Def_ProdHedgeCVaR_Joint_Model`): a valid terminal-time model with parameters $p,c,\tilde\sigma,T,C>0$, $\eta\ne0$, and $s(m,Q)$ the optimal value of the static hedging problem (28). Problem (36) is
--
--   $$\max_{m\ge0,\,Q\ge0}\Big\{m-\frac{1}{1-\alpha}\,s(m,Q)\Big\}\quad\text{s.t. } m-pQ+C\ge0.$$
--
--   Let $\alpha\in(0,1)$, let $\lambda^\circ$ solve the first equation of (45), $\mathsf E[(1-\lambda Z_T)^+]=\alpha$, and let $Q^\circ$ solve the second equation of (45) at $\lambda^\circ$, $(p+c)\,\mathsf E[(\lambda^\circ Z_T)\wedge\Delta(Q^\circ)]=p(1-\alpha)$. Put $C^\circ=(p+c)\,\mathsf E^M[(Q^\circ-\hat D_T^+(\lambda^\circ))^+]$ (46).
--
--   **Claim (Theorem 2 (ii)).** Suppose $C\le C^\circ$, and let $(\lambda^*,Q^*)$ with $\lambda^*\ge0$ solve the system formed by (53),
--
--   $$(p+c)\,\mathsf E^M[(Q-\hat D_T^+(\lambda))^+]=C,$$
--
--   and the second equation of (45), $(p+c)\,\mathsf E[(\lambda Z_T)\wedge\Delta(Q)]=p(1-\alpha)$. Then problem (36) has exactly one optimal solution, namely $(m^*_\alpha,Q^*_\alpha)=(pQ^*-C,\,Q^*)$: the budget constraint binds.
--
--   Formally: the set of optimal solutions of (36) is the singleton $\{(pQ^*-C,Q^*)\}$. This is the optimality part of case (ii) of Theorem 2 (existence and uniqueness of $(\lambda^*,Q^*)$ is the milestone `eq_53_system`).
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), p. 20, Theorem 2 (part (ii), the optimal-solution claim)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- Theorem 2 (ii), p. 20: if C ≤ C°, and (λ*, Q*) with λ* ≥ 0 solves (53) together with the
second equation of (45), then the optimal solution of (36) is unique and equals (pQ* − C, Q*). -/
theorem theorem_2_optimum_binding {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC QC : ℝ)
    (hlamC : M.IsLamC α lamC) (hQC : M.IsQC α lamC QC) (hC : M.θ.C ≤ M.CC lamC QC)
    (lamS QS : ℝ) (hlamS : 0 ≤ lamS) (h53 : M.Eq53 lamS QS) (hQS : M.IsQC α lamS QS) :
    {x | M.IsOptimal36 α x} = {(M.θ.p * QS - M.θ.C, QS)} := by sorry

end ProdHedgeCVaR.Joint
