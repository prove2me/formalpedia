-- Prove2me | Theorems.Thm_PrepoLocal_Threshold_cost_identity
-- name    : PrepoLocal.Threshold.cost_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:51.097242+00:00
-- url     : https://prove2.me/theorems/05d81225-21f7-45a4-83c6-b1253bbbb0f0
-- title:
--   §3, p. 7 — cost identity: C(x) = αµ_D + iµ_T x + (1 − α)E[S(x)] + (v − 1)E[(S(x) − x)⁺]
-- statement:
--   In the single-cycle prepo model (parameters $0<\alpha<1$, $i\ge0$, $v>1$, $b\ge0$, $\gamma\ge0$; integrable, nonnegative $D,Q,R,T$ with $T$ independent of $(D,Q,R)$), let $S(x)=(D-\min\{Q,\hat b(x,R,T)/\alpha\})^+$ be the local shortage and
--   $$
--   C(x)=\mathbb E\bigl[iTx+\alpha\min\{D,Q,\hat b(x,R,T)/\alpha\}+\min\{x,S(x)\}+v(S(x)-x)^+\bigr]
--   $$
--   the expected cycle cost. Then, for every prepo level $x$,
--   $$
--   C(x)=\alpha\mu_D+i\mu_T x+(1-\alpha)\,\mathbb E[S(x)]+(v-1)\,\mathbb E\bigl[(S(x)-x)^+\bigr].
--   $$
--
--   The identity rewrites the operational cost (holding, local purchase, prepo used, unmet demand) as a fixed local-purchase cost plus weighted local and global shortages; it is the form in which the paper analyzes $C$.
--
--   **Formalization Note** The identity is stated for every real $x$, which includes the feasible range $0\le x\le b$ of the paper.
-- source:
--   Eftekhar, Song & Webster, Pre-Positioning and Local-Purchasing for Emergency Operations Under Budget and Supply Uncertainty, SSRN 3210309 (revision of Aug. 13, 2020), p. 7, §3, display of C(x)

import Mathlib
import Definitions.Def_PrepoLocal_Threshold_Model
open MeasureTheory ProbabilityTheory

namespace PrepoLocal.Threshold

/-- §3, p. 7: the two expressions of the expected cycle cost agree,
`C(x) = αμ_D + iμ_T x + (1 − α) E[S(x)] + (v − 1) E[(S(x) − x)⁺]`. -/
theorem cost_identity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ) (x : ℝ) :
    C P μ E x = P.al * (∫ ω, E.D ω ∂μ) + P.hold * (∫ ω, E.T ω ∂μ) * x
      + (1 - P.al) * (∫ ω, S P E x ω ∂μ)
      + (P.v - 1) * (∫ ω, max (S P E x ω - x) 0 ∂μ) := by sorry

end PrepoLocal.Threshold
