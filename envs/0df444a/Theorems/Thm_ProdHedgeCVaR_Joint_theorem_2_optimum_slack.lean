-- Prove2me | Theorems.Thm_ProdHedgeCVaR_Joint_theorem_2_optimum_slack
-- name    : ProdHedgeCVaR.Joint.theorem_2_optimum_slack
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-29T09:24:36.144486+00:00
-- url     : https://prove2.me/theorems/4cd25939-3dc6-4ef4-b324-24e774d38f75
-- title:
--   Theorem 2 (i), p. 20 — if C ≥ C°, the unique optimal solution of (36) is (m°, (Q°)⁺)
-- statement:
--   Throughout, the setting is that of the goal theorem `ProdHedgeCVaR.Joint.theorem_2` (the definitions of `Definitions.Def_ProdHedgeCVaR_Joint_Model`): a valid terminal-time model with parameters $p,c,\tilde\sigma,T,C>0$, $\eta\ne0$, and $s(m,Q)$ the optimal value of the static hedging problem (28). Problem (36) is
--
--   $$\max_{m\ge0,\,Q\ge0}\Big\{m-\frac{1}{1-\alpha}\,s(m,Q)\Big\}\quad\text{s.t. } m-pQ+C\ge0.$$
--
--   Let $\alpha\in(0,1)$, let $\lambda^\circ$ solve the first equation of (45), $\mathsf E[(1-\lambda Z_T)^+]=\alpha$, and let $Q^\circ$ solve the second equation of (45) at $\lambda^\circ$, $(p+c)\,\mathsf E[(\lambda^\circ Z_T)\wedge\Delta(Q^\circ)]=p(1-\alpha)$. Put $C^\circ=(p+c)\,\mathsf E^M[(Q^\circ-\hat D_T^+(\lambda^\circ))^+]$ (46).
--
--   **Claim (Theorem 2 (i)).** If $C\ge C^\circ$, then problem (36) has exactly one optimal solution, namely
--
--   $$(m^*_\alpha,Q^*_\alpha)=\big(m^\circ,(Q^\circ)^+\big),\qquad m^\circ=p(Q^\circ)^+-C+\frac{C-C^\circ}{\mathsf P^M(\lambda^\circ Z_T\le1)}\ \text{(50)}.$$
--
--   Formally: the set of optimal solutions of (36) is the singleton $\{(m^\circ,(Q^\circ)^+)\}$. This is the optimality part of case (i) of Theorem 2; the remaining claims of Theorem 2 have been reduced to the mission's milestones.
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), p. 20, Theorem 2 (part (i), the optimal-solution claim)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_ProdHedgeCVaR_Joint_Model

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory Filter Topology

/-- Theorem 2 (i), p. 20: if C ≥ C°, the optimal solution of (36) is unique and equals
(m°, (Q°)⁺), with λ° and Q° the solutions of (45), C° from (46) and m° from (50). -/
theorem theorem_2_optimum_slack {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : M.Valid)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (lamC QC : ℝ)
    (hlamC : M.IsLamC α lamC) (hQC : M.IsQC α lamC QC) (hC : M.CC lamC QC ≤ M.θ.C) :
    {x | M.IsOptimal36 α x} = {(M.mC lamC QC, max QC 0)} := by sorry

end ProdHedgeCVaR.Joint
