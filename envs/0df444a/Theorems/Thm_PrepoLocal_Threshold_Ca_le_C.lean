-- Prove2me | Theorems.Thm_PrepoLocal_Threshold_Ca_le_C
-- name    : PrepoLocal.Threshold.Ca_le_C
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:58.406979+00:00
-- url     : https://prove2.me/theorems/daeef252-282a-4611-8018-5dccdb7e81c7
-- title:
--   §4.1, p. 9 — relaxing the local budget constraint lowers the cost: Ca(x) ≤ C(x)
-- statement:
--   In the single-cycle prepo model (standing assumptions as in the model definition), let $C$ be the expected cycle cost and
--   $$
--   C_a(x)=\alpha\mu_D+i\mu_T x+(1-\alpha)\,\mathbb E[(D-Q)^+]+(v-1)\,\mathbb E[(D-Q-x)^+]
--   $$
--   the cost of the auxiliary model, in which the local budget constraint is relaxed: $\min\{Q,\hat b(x,R,T)/\alpha\}$ is replaced with $Q$. Then for every prepo level $x$,
--   $$
--   C_a(x)\le C(x).
--   $$
--
--   The auxiliary model is the relaxation of problem $\Pi$ that the paper introduces on p. 9; this inequality is what makes its cost a lower bound on the true cost, and it is one of the two ingredients of Proposition 2(b).
--
--   **Formalization Note** The inequality is stated for every real $x$. It is not printed as a display in the paper; it is the content of the sentence on p. 9 defining the auxiliary model as a relaxation.
-- source:
--   Eftekhar, Song & Webster, Pre-Positioning and Local-Purchasing for Emergency Operations Under Budget and Supply Uncertainty, SSRN 3210309 (revision of Aug. 13, 2020), p. 9, §4.1, definition of the auxiliary model

import Mathlib
import Definitions.Def_PrepoLocal_Threshold_Model
open MeasureTheory ProbabilityTheory

namespace PrepoLocal.Threshold

/-- §4.1, p. 9: relaxing the local budget constraint (replacing `min{Q, b̂/α}` by `Q`)
can only lower the expected cycle cost: `Ca(x) ≤ C(x)`. -/
theorem Ca_le_C {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ) (x : ℝ) :
    Ca P μ E x ≤ C P μ E x := by sorry

end PrepoLocal.Threshold
