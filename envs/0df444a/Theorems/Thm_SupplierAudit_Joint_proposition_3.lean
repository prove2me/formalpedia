-- Prove2me | Theorems.Thm_SupplierAudit_Joint_proposition_3
-- name    : SupplierAudit.Joint.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:31:38.527981+00:00
-- url     : https://prove2.me/theorems/2516d174-424e-4328-bbbd-ee0ab090b6bd
-- title:
--   Proposition 3 — a stable joint-auditing coalition audits the common supplier, and $S_1$ too when $K<K^L_c$
-- statement:
--   Two competing buyers ($0<\beta\le1$) share a common supplier $S_c$ and each has an independent supplier. They may form a coalition that audits jointly: it chooses efforts $(e_{c1},e_{cc},e_{c2})\in[0,1]^3$ on $S_1,S_c,S_2$, auditing at most two suppliers, and pays $K\mathbf 1\{e_{cj}>0\}+\tfrac a2e_{cj}^2$ per audited supplier. The buyers still compete downstream. Assume the standing conditions of the model and the Sec. 4.3 scenario $\pi^b(0,0)\ge\pi^b(d_M,0)\ge\pi^b(d_M,d_M)\ge\pi^b(2d_M,d_M)\ge\pi^b(2d_M,2d_M)$. Assume also the interior-effort condition $\hat e_I<1$ of the unilateral benchmark. Write $\Pi^b$ for the coalition's aggregate expected profit, $R^b_i$ for buyer $B_i$'s expected profit excluding auditing costs, $\Delta\Pi=R^b_1-R^b_2$, and $\Gamma_i$ for the cost shares of eq. (3).
--
--   **Stability.** For every $K\ge0$, every equilibrium $(s_1,s_2)$ of unilateral auditing (with the tie-breaking rule) and every optimal feasible joint plan $x$:
--   $$\Pi^b_1(s_1;s_2)+\Pi^b_2(s_2;s_1)\le\Pi^b(x),$$
--   and if $s_1=s_2$, also $\Pi^b_i(s_i;s_{i'})\le R^b_i(x)-\Gamma_i$ for $i=1,2$.
--
--   **Optimal joint audits.** There are thresholds $K^L_c\le K^H_c$ such that, for every $K\ge0$:
--
--   1. if $K<K^L_c$, an optimal plan audits $S_1$ and $S_c$ ($e^*_{c1}>0$, $e^*_{cc}>0$, $e^*_{c2}=0$), and at it $\Delta\Pi>0$;
--   2. if $K^L_c\le K<K^H_c$, an optimal plan audits only $S_c$ ($e^*_{c1}=0$, $e^*_{cc}>0$, $e^*_{c2}=0$), and at it $\Delta\Pi=0$;
--   3. if $K\ge K^H_c$, auditing no supplier is optimal.
--
--   Unilateral auditing never audits the common supplier (Proposition 2). The joint-auditing coalition audits it whenever it audits anything, and the cost shares (3) leave both buyers equally well off.
--
--   **Formalization Note** "Yields the highest aggregate profit" means that some maximizer has the stated pattern; uniqueness is not claimed. Each firm's stability condition is stated against the symmetric unilateral equilibria only: against the asymmetric equilibrium of Proposition 2(ii), whose case the paper omits as "similar", it can fail (see the milestone on part (3) of the proof). "Higher" is stated as $\ge$, which is what the proof gives. The interior-effort assumption of p. 10 is encoded as $\hat e_I<1$.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Proposition 3, pp. 13–14; Sec. 4.3, p. 13; eq. (3), p. 14; proof pp. ec12–ec14 (PDF 40–42)

import Mathlib
import Definitions.Def_SupplierAudit_Joint_Model

namespace SupplierAudit.Joint

/-- Proposition 3, pp. 13–14 (optimal joint-auditing decisions and cost sharing), under the
standing assumptions (`Params`), `β ∈ (0,1]`, the Sec. 4.3 scenario ordering and the interior-effort
assumption `ê_I < 1`.

Stability: at every optimal joint plan `x`, the coalition earns in aggregate at least what the buyers
earn in any unilateral equilibrium, and each buyer, after paying its share (3), earns at least its
profit in a symmetric unilateral equilibrium.

Structure: there are thresholds `K^L_c ≤ K^H_c` such that, for `0 ≤ K`, an optimal plan audits `S₁`
and `S_c` with `∆Π > 0` when `K < K^L_c`, only `S_c` with `∆Π = 0` when `K^L_c ≤ K < K^H_c`, and auditing
no supplier is optimal when `K ≥ K^H_c`. -/
theorem proposition_3 (P : SupplierAudit.Competition.Params) (hβ : 0 < P.β) (hscen : Scenario P) (hint : SupplierAudit.Competition.eHatI P < 1) :
    (∀ K : ℝ, 0 ≤ K → ∀ s₁ s₂ : Strategy, IsEquilibrium P K s₁ s₂ →
      ∀ x ∈ Feasible, IsMaxOn (aggProfit P K) Feasible x →
        unilProfit₁ P K s₁ s₂ + unilProfit₂ P K s₁ s₂ ≤ aggProfit P K x ∧
        (s₁ = s₂ →
          unilProfit₁ P K s₁ s₂ ≤ jointG₁ P x - Gamma₁ P K x ∧
          unilProfit₂ P K s₁ s₂ ≤ jointG₂ P x - Gamma₂ P K x)) ∧
    ∃ KL KH : ℝ, KL ≤ KH ∧ ∀ K : ℝ, 0 ≤ K →
      (K < KL → ∃ x ∈ Feasible, IsMaxOn (aggProfit P K) Feasible x ∧
          0 < x.1 ∧ 0 < x.2.1 ∧ x.2.2 = 0 ∧ 0 < deltaPi P x) ∧
      (KL ≤ K → K < KH → ∃ x ∈ Feasible, IsMaxOn (aggProfit P K) Feasible x ∧
          x.1 = 0 ∧ 0 < x.2.1 ∧ x.2.2 = 0 ∧ deltaPi P x = 0) ∧
      (KH ≤ K → IsMaxOn (aggProfit P K) Feasible (0, 0, 0)) := by sorry

end SupplierAudit.Joint
