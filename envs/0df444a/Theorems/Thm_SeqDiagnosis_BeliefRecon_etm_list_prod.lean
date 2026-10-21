-- Prove2me | Theorems.Thm_SeqDiagnosis_BeliefRecon_etm_list_prod
-- name    : SeqDiagnosis.BeliefRecon.etm_list_prod
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:59.950564+00:00
-- url     : https://prove2.me/theorems/3190ac4a-4360-496b-aa39-6b0a2f998bc4
-- title:
--   Proof of Theorem 1, p. ec1 — product identity for exponential tilting
-- statement:
--   Let $f_j(y)=f_0(y)\exp\{\beta_{j0}+\beta_j^{\mathsf T}h(y)\}$ for a nonbaseline class $j$. For any arrival-ordered list $y_1,\ldots,y_t$, including the empty list,
--
--   $$\prod_{m=1}^t f_j(y_m)=\left(\prod_{m=1}^t f_0(y_m)\right)\exp\left\{t\beta_{j0}+\beta_j^{\mathsf T}\sum_{m=1}^t h(y_m)\right\}.$$
--
--   The product identity rewrites the likelihood of a full observation sequence using the baseline likelihood and one cumulative statistic.
--
--   **Formalization Note** The model's standing density and integrability assumptions are explicit. An empty product is one, and the displayed identity also holds when $t=0$.
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, p. ec1 (PDF 38), proof of Theorem 1, exponential-tilting display

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Model

open Matrix

namespace SeqDiagnosis.BeliefRecon

/-- Multiplication of the exponential-tilting identity over an observation list. -/
theorem etm_list_prod {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) (hS : M.Standing) (hETM : M.ETM)
    (j : Fin N) (ys : List Y) :
    (ys.map (M.f j.succ)).prod = (ys.map (M.f 0)).prod *
      Real.exp ((ys.length : ℝ) * M.normConst (M.beta j) + M.beta j ⬝ᵥ (ys.map M.h).sum) := by sorry

end SeqDiagnosis.BeliefRecon
