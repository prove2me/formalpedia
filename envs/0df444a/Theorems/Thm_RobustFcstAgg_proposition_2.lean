-- Prove2me | Theorems.Thm_RobustFcstAgg_proposition_2
-- name    : RobustFcstAgg.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:13.798436+00:00
-- url     : https://prove2.me/theorems/1e3d5e78-0bf3-446b-a1f0-d808bbe82e44
-- title:
--   Proposition 2 — $\mathcal Q_{\mathrm{inter}(d)}$ is DAG-elicitable with order and agent complexity at most $d$
-- statement:
--   For all $n$ and $d$, the collection $\mathcal Q_{\mathrm{inter}(d)}=(\mathrm{inter}(S))_{1\le|S|\le d}$ is DAG-elicitable, with
--   $$\text{query-c}(\mathcal Q_{\mathrm{inter}(d)})=m_d=\sum_{k=1}^d\binom nk,\qquad\text{order-c}(\mathcal Q_{\mathrm{inter}(d)})\le d,\qquad\text{agent-c}(\mathcal Q_{\mathrm{inter}(d)})\le d,$$
--   and a single DAG witnesses both bounds.
--
--   This is what puts the linear intersection rules in the class $\mathcal A^{\mathrm{ord}}_d$, so it supplies the upper-bound side of the reduction.
--
--   Differences from the source:
--   - generalization: DAG-elicitable (Definition 3) → the eliciting DAG also satisfies Condition 1; reason: a stronger conclusion, which implies the printed one; p.25 notes that the Brier score satisfies Condition 1
--   - reading: a payment function π(r, R) exists (Definition 2) → one π for all instances D; reason: the principal does not know D (p.4); it matters only for the upper-bound class, which uses the quadratic score
--   - reading: the expectations E_D[π(r, R) | S_i] (Definition 2) and E[(A − Y)²] (Eq. (1)) → the payment is integrable on a.e. fibre for every report r, and in the class A^ord_d the randomized output is jointly a.e.-measurable in (z, signals); reason: the expectations the source writes presuppose both; the linear intersection rules satisfy both
--   - reading: agent(inter(S)) is an expert of S → the minimum of S; reason: every choice gives the same random variable and the same complexities
--   - encoding: order-c ≤ d and agent-c ≤ d → one DAG with every walk from a query of length ≤ d, and at most d experts reachable; reason: the definitions of p.6 for a witnessing DAG
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Proposition 2, p.9

import Mathlib
import Definitions.Def_RobustFcstAgg_InterIndex
import Definitions.Def_RobustFcstAgg_interQuery
import Definitions.Def_RobustFcstAgg_IsDAGElicits
import Definitions.Def_RobustFcstAgg_OrderLE
import Definitions.Def_RobustFcstAgg_AgentLE

namespace RobustFcstAgg

/-- **Proposition 2.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Proposition 2, p.9: "`Q_inter(d)` is DAG-elicitable, with `query-c(Q_inter(d)) = m_d`,
`order-c(Q_inter(d)) ≤ d`, and `agent-c(Q_inter(d)) ≤ d`. Each bound is simultaneously witnessed by a single DAG `G`."

**Formalization Note.** `IsDAGElicits` includes Condition 1, so this also says that the quadratic score meets it (p.25). -/
theorem proposition_2 (n d : ℕ) :
    (∃ out : InterIndex n d → Finset (Option (InterIndex n d)),
      IsDAGElicits (fun S : InterIndex n d => interQuery S.1 S.2.1) out ∧
      OrderLE out d ∧
      AgentLE (fun S : InterIndex n d => interQuery S.1 S.2.1) out d) ∧
    Fintype.card (InterIndex n d) = ∑ k ∈ Finset.Icc 1 d, n.choose k := by sorry

end RobustFcstAgg
