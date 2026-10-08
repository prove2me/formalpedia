-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_eq_2_2
-- name    : SchalAvg.AvgOpt.eq_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:50.378327+00:00
-- url     : https://prove2.me/theorems/9a9d065e-6bbe-4887-b25f-96ace3ab2911
-- title:
--   (2.2) — the relative discounted optimality equation w_β + (1 − β)m_β = c + β∫w_β dq along f_β
-- statement:
--   In Schäl's decision model $(S, A, A(\cdot), q, c)$ assume the General Assumption $g < \infty$ and Condition (W) or Condition (S). Let $0 < \beta < 1$ and let $f_\beta$ be a $\beta$-discount optimal stationary policy. Then the relative discounted value function $w_\beta = v_\beta - m_\beta$ satisfies
--   $$w_\beta(x) + (1 - \beta) m_\beta = c(x, f_\beta(x)) + \beta \int w_\beta \, dq(x, f_\beta(x)), \qquad x \in S.$$
--
--   This equation is the starting point for producing the average cost optimality inequality of Proposition 1.3 in the limit $\beta \to 1$.
--
--   **Formalization Note.** $w_\beta$ is the truncated difference $v_\beta - m_\beta$ in $[0, \infty]$; the General Assumption implies $m_\beta < \infty$, so it is the true difference ($v_\beta \ge m_\beta$ by definition). The paper derives (2.2) "as a consequence" of Proposition 2.1, whose hypotheses ((W) or (S), $f_\beta$ discount optimal) are carried here.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), p. 166, (2.2)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem eq_2_2 {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [TopologicalSpace S]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model S A) (hGA : GeneralAssumption M) (hWS : CondW M ∨ CondS M)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (f : S → A) (hf : IsDiscOptimal M β f) (x : S) :
    wβ M β x + ENNReal.ofReal (1 - β) * mβ M β =
      M.toMDP.cost x (f x) + ENNReal.ofReal β * ∫⁻ y, wβ M β y ∂(M.toMDP.q (x, f x)) := by sorry

end SchalAvg.AvgOpt
