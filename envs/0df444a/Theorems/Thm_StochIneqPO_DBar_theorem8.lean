-- Prove2me | Theorems.Thm_StochIneqPO_DBar_theorem8
-- name    : StochIneqPO.DBar.theorem8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:31.236213+00:00
-- url     : https://prove2.me/theorems/70e74d5a-918e-405e-b94a-e5ddaf13c5e4
-- title:
--   Theorem 8 — Ornstein's d̄ as a supremum over stationary common lower laws
-- statement:
--   Let $P,Q$ be stationary laws of real-valued two-sided processes, with integrable time-zero coordinates. Among stationary laws $R$ that are stochastically below both $P$ and $Q$, take the supremum of the time-zero mean. Then this supremum is finite and
--
--   $$\bar d(P,Q)=\int\omega^0\,P(d\omega)+\int\omega^0\,Q(d\omega)-2\sup_{\substack{R\in\mathcal S_T\\R\prec P,\,R\prec Q}}\int\omega^0\,R(d\omega).$$
--
--   This replaces the infimum over stationary couplings by an optimization over single stationary laws.
--
--   **Formalization Note** Integrability of $\omega^0$ under $P,Q$ makes explicit the standing assumption of Section 8 (the integrals of $\omega^0$ under $P$ and $Q$ are defined and finite). The formal supremum uses only $R$ with integrable $\omega^0$; laws with undefined or negative-infinite means do not alter the supremum, and the optimal meet law is integrable. `IsLUB` states existence of a finite least upper bound and avoids a totalized real supremum at an empty or unbounded set.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Theorem 8, equation (18), p. 910 (PDF p. 12)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_dbar

namespace StochIneqPO.DBar

open MeasureTheory

/-- Theorem 8, equation (18), p. 910: Ornstein's distance in terms of a common lower law. -/
theorem theorem8
    (P Q : Measure (ℤ → ℝ))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q) :
    ∃ s : ℝ,
      IsLUB {r : ℝ | ∃ R : Measure (ℤ → ℝ),
        IsShiftInvariant R ∧ Integrable (fun ω : ℤ → ℝ => ω 0) R ∧
        StochIneqPO.Comparison.StochLE R P ∧ StochIneqPO.Comparison.StochLE R Q ∧ r = ∫ ω, ω 0 ∂ R} s ∧
      dbar P Q = (∫ ω, ω 0 ∂P) + (∫ ω, ω 0 ∂Q) - 2 * s := by sorry

end StochIneqPO.DBar
