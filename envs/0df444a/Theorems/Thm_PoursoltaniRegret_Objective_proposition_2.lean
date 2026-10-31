-- Prove2me | Theorems.Thm_PoursoltaniRegret_Objective_proposition_2
-- name    : PoursoltaniRegret.Objective.proposition_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:57:23.112538+00:00
-- url     : https://prove2.me/theorems/fb360a03-feda-42f5-b19d-2e40dd4b677c
-- title:
--   Proposition 2 — absolute-regret reformulation with objective uncertainty (as printed)
-- statement:
--   Let $W,v,P,q,A,B,\psi,c,D,d$ be arbitrary real objective-uncertainty data of the finite dimensions specified in the model. Put $X=\{x:Wx\le v\}$, $U=\{\zeta:P\zeta\le q\}$, $Y(x)=\{y:Ax+By\le\psi\}$ and $d(\zeta)=D\zeta+d$. Suppose Assumptions 1 and 2 hold: a feasible triple exists, and every $x\in X$ admits recourse for every $\zeta\in U$.
--
--   Let $R(x)$ be the nested worst-case absolute regret and $R^*=\inf_{x\in X}R(x)$. Use the literal printed set
--   $$U'=\{(\zeta,\rho):\zeta\in U,\ B^T\rho=d(\zeta)\},$$
--   with unrestricted $\rho$. Let $V(x)$ be the supremum over all lifted-scenario policies $(\lambda,\gamma)$ satisfying $\lambda,\gamma\ge0$, $A^T\lambda+W^T\gamma=c$, and $B^T\lambda=d(\zeta)$ at every scenario, of the infimum over $U'$ of
--   $$c^Tx+(\psi-Ax)^T\rho-\psi^T\lambda(\zeta,\rho)-v^T\gamma(\zeta,\rho).$$
--   Write $V^*=\sup_{x\in X}V(x)$. The proposition asserts
--   $$\forall x\in X:\ R(x)=-V(x),\qquad R^*=-V^*,\qquad\{x\in X:R(x)=R^*\}=\{x\in X:V(x)=V^*\}.$$
--   Furthermore,
--   $$(A3\wedge A5)\Longrightarrow(A1'\wedge A2'\wedge A3'),\qquad(A3\wedge A5\wedge A4)\Longrightarrow A4'.$$
--   Here $A3$ is bounded recourse at some scenario for each first-stage decision; $A4$ is a lower bound on worst-case profit for each such decision; $A5$ is a uniform upper bound on all profits. The primed predicates apply to the independently constructed transformed recourse problem. Only $A1$ and $A2$ are base hypotheses. No optimizing first-stage decision or policy is assumed to exist.
--
--   This is the source's exact-reformulation claim, including all assumption-transfer clauses. The printed uncertainty set omits $\rho\ge0$, making the claim false on the concrete instance recorded in INSIGHTS.yaml; the target deliberately preserves that source statement.
--
--   **Formalization Note** Optimization values lie in $\mathrm{EReal}$. Regret takes the supremum over scenario, hindsight decision and hindsight recourse, followed by an infimum over actual recourse, of a real profit difference. The unbounded-below reporting convention is not substituted into the raw objective. First-stage optimality refers to attainment of the optimized first-stage envelope, without asserting policy attainment.
--
--   Differences from the source:
--   - encoding: finite-dimensional real vectors and concatenated block matrices → Fin-indexed real vectors, products for lifted vectors, and expanded component constraints; reason: a coordinate representation of exactly the same feasible sets and objectives
--   - encoding: Section 4 nested optimization convention and equivalence of minimization with maximization → EReal extrema of real objective differences, opposite value signs, and equality of first-stage optimizer sets; reason: retains empty and unbounded cases without subtracting infinities or asserting attainment
--   - reading: (16b) suppresses the scenario quantifier → policy feasibility at every lifted scenario in the printed set; reason: the universal quantifier is explicit in the defining TSLRO (1b)
--   - generalization: equivalence of the optimization problems → also equality of negative policy-envelope value and regret at every feasible first-stage decision; reason: makes the fixed-decision comparison used in Appendix F.3 explicit and implies the full value and optimizer claims
-- source:
--   Poursoltani and Delage (2022), Adjustable Robust Optimization Reformulations of Two-Stage Worst-Case Regret Minimization Problems, Operations Research, https://doi.org/10.1287/opre.2021.2159; supplied source.pdf (dated July 10, 2020; printed page = PDF page); Proposition 2, pp. 9–10, all clauses; §4 nested convention, p. 8; Appendix F.3, pp. 31–32

import Definitions.Def_PoursoltaniRegret_Objective_Regret
import Definitions.Def_PoursoltaniRegret_Objective_Lift

namespace PoursoltaniRegret.Objective

theorem proposition_2 {nx ny nz m r s : ℕ} (M : Model nx ny nz m r s)
    (h1 : M.assumption1) (h2 : M.assumption2) :
    (∀ x ∈ M.firstStage, M.regretAt x = -M.liftBestAt x) ∧
    M.regretValue = -M.liftValue ∧
    (∀ x, M.isRegretOptimal x ↔ M.isLiftFirstStageOptimal x) ∧
    ((M.assumption3 ∧ M.assumption5) →
      M.liftAssumption1 ∧ M.liftAssumption2 ∧ M.liftAssumption3) ∧
    ((M.assumption3 ∧ M.assumption5 ∧ M.assumption4) → M.liftAssumption4) := by sorry

end PoursoltaniRegret.Objective
