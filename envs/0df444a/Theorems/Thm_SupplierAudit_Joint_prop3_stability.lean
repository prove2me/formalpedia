-- Prove2me | Theorems.Thm_SupplierAudit_Joint_prop3_stability
-- name    : SupplierAudit.Joint.prop3_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:31:29.961282+00:00
-- url     : https://prove2.me/theorems/aae916ee-e92c-405b-bd58-368d46375e49
-- title:
--   Proof of Prop. 3, part (3) — stability of the joint-auditing coalition against unilateral auditing
-- statement:
--   Consider competing buyers ($0<\beta\le1$) in the Sec. 4.3 scenario $\pi^b(0,0)\ge\pi^b(d_M,0)\ge\pi^b(d_M,d_M)\ge\pi^b(2d_M,d_M)\ge\pi^b(2d_M,2d_M)$, under the interior-effort assumption $\hat e_I<1$, where $\hat e_I$ is eq. (2). Let $K\ge0$ and let $(s_1,s_2)$ be an equilibrium of unilateral auditing, with the paper's tie-breaking rule. Let $x$ be a feasible joint plan that maximizes the coalition's aggregate profit $\Pi^b$. Then:
--
--   1. (aggregate) $\Pi^b_1(s_1;s_2)+\Pi^b_2(s_2;s_1)\le\Pi^b(x)$;
--   2. (each firm) if the equilibrium is symmetric, $s_1=s_2$, then after paying its cost share $\Gamma_i$ of eq. (3) each buyer earns at least its unilateral profit:
--   $$\Pi^b_1(s_1;s_2)\le R^b_1(x)-\Gamma_1,\qquad \Pi^b_2(s_2;s_1)\le R^b_2(x)-\Gamma_2.$$
--
--   These are conditions (a) and (b) of Sec. 4.3 for a stable coalition. The symmetric equilibria are the one in which both buyers audit their independent suppliers with effort $e^*_I$ and the one in which neither audits.
--
--   **Formalization Note** The paper proves condition (b) only against the symmetric equilibrium (its type A, and the omitted no-audit case) and says the asymmetric type B, where one buyer audits with $\hat e_I$ and the other audits nothing, "is similar". It is not. Take $\alpha=10$, $\beta=1$, $w=1$, $\hat w=3$, $d_M=1/2$, $e=1/10$, $r=1$, $a=50$ and $K=0.2$; all standing assumptions and the scenario hold. There the type-B profile is an equilibrium and auditing no supplier is optimal for the coalition. The auditing buyer then earns more unilaterally than half the coalition's optimum. Condition (b) is therefore stated for symmetric equilibria only. "Higher" is proved, and stated, as $\ge$.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), proof of Proposition 3, part (3), p. ec14 (PDF 42); stability conditions, Sec. 4.3, p. 13; tie-breaking rule and interior efforts, p. 10; eq. (2), p. 11

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model

namespace SupplierAudit.Joint

/-- Proof of Proposition 3, part (3), p. ec14: at every optimal joint plan, the coalition's aggregate
profit is at least the buyers' aggregate profit in any unilateral equilibrium (condition (a), p. 13),
and, against a symmetric unilateral equilibrium (both buyers audit their independent suppliers with
the same effort, or neither audits), each buyer's joint-auditing profit after paying its cost share is
at least its unilateral profit (condition (b)). Against the asymmetric equilibrium of Proposition 2(ii)
condition (b) can fail; see the mission's formalization notes. -/
theorem prop3_stability (P : SupplierAudit.Competition.Params) (hβ : 0 < P.β) (hscen : Scenario P) (hint : SupplierAudit.Competition.eHatI P < 1)
    (K : ℝ) (hK : 0 ≤ K) (s₁ s₂ : Strategy) (heq : IsEquilibrium P K s₁ s₂)
    (x : ℝ × ℝ × ℝ) (hx : x ∈ Feasible) (hmax : IsMaxOn (aggProfit P K) Feasible x) :
    unilProfit₁ P K s₁ s₂ + unilProfit₂ P K s₁ s₂ ≤ aggProfit P K x ∧
    (s₁ = s₂ →
      unilProfit₁ P K s₁ s₂ ≤ jointG₁ P x - Gamma₁ P K x ∧
      unilProfit₂ P K s₁ s₂ ≤ jointG₂ P x - Gamma₂ P K x) := by sorry

end SupplierAudit.Joint
