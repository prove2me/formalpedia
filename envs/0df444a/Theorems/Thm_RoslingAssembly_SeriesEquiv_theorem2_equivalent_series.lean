-- Prove2me | Theorems.Thm_RoslingAssembly_SeriesEquiv_theorem2_equivalent_series
-- name    : RoslingAssembly.SeriesEquiv.theorem2_equivalent_series
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:38.595247+00:00
-- url     : https://prove2.me/theorems/7f25a4e9-a47d-4771-b845-041e6b26212f
-- title:
--   Theorem 2 — equivalent series optimal policies
-- statement:
--   Suppose Rosling’s Assumption holds and the assembly system starts in long-run balance. Every policy optimal for Problem P is optimal for the equivalent pure series system with lead times $L_i$, the same shortage coefficient $p+H_1$, and holding coefficients $h_i\alpha^{l_i-L_i}$. If Problem P has an optimal policy, every series-optimal policy is also optimal for P. Thus their optimal-policy sets coincide whenever P attains its minimum.
--
--   $$\operatorname{Opt}(P)\subseteq\operatorname{Opt}(P_{\mathrm{series}}),\qquad \operatorname{Opt}(P)\ne\varnothing\Longrightarrow\operatorname{Opt}(P_{\mathrm{series}})\subseteq\operatorname{Opt}(P).$$
--
--   The result reduces the policy comparison for an assembly tree to a pure series system.
--
--   **Formalization Note** Discounting is restricted to $0<\alpha<1$. The converse is conditional on existence of a P optimum. The zero-lead-time boundary and well-formed initial pipeline are explicit repairs to assumptions implicit or missing in the printed statement. Feasibility is almost sure.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, p. 569, Theorem 2

import Definitions.Def_RoslingAssembly_SeriesEquiv_Cost

namespace RoslingAssembly.SeriesEquiv

/-- Rosling, Theorem 2, p. 569: equality of optimal policy classes for
the assembly and equivalent pure series systems. -/
theorem theorem2_equivalent_series (S : Model) (x0 : InitialPositions)
    [MeasureTheory.IsProbabilityMeasure S.ν]
    (hTree : S.ValidTree) (hDemand : S.ValidDemand)
    (hα : 0 < S.α ∧ S.α < 1) (hAssumption : S.Assumption)
    (hInitial : S.WellFormedInitial x0)
    (hBalance : S.InitiallyBalanced x0)
    (hZero : S.ZeroLeadBoundary x0) :
    (∀ π : Policy, S.Optimal x0 π → (S.series).Optimal x0 π) ∧
    ((∃ π : Policy, S.Optimal x0 π) →
      ∀ π : Policy, (S.series).Optimal x0 π → S.Optimal x0 π) := by sorry

end RoslingAssembly.SeriesEquiv
