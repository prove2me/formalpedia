-- Prove2me | Theorems.Thm_PutermanMDP_SemiMarkov_evaluation_identifies_gain
-- name    : PutermanMDP.SemiMarkov.evaluation_identifies_gain
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:58.709988+00:00
-- url     : https://prove2.me/theorems/a14dbfb3-2baa-4236-94fd-d546af707d39
-- title:
--   Theorem 11.4.2 — evaluation equation identifies the gain
-- statement:
--   Let $S$ be nonempty and countable, and fix a stationary randomized rule $d$. Assume that its embedded chain is unichain, its Cesaro limit is a probability matrix, and Assumption 11.1.1 holds. The finite-epoch reward and time expectations are finite. If a real constant $g$ and a real function $h$ satisfy
--   $$h=r_d-g y_d+M_dh,$$
--   with each transition expectation of $h$ absolutely convergent, then
--   $$g^{d^\infty}(s)=g\qquad(s\in S).$$
--   This is the printed gain-identification assertion. The statement deliberately retains an arbitrary, possibly unbounded $h$; finding F1 and its draft verification F4 show that this literal formulation is false.
--
--   **Formalization Note** The finite-moment predicates specify the real-expectation domain. They do not impose invariant integrability or boundedness of $h$. The extended gain is asserted equal to the real scalar $g$.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, https://doi.org/10.1002/9780470316887, p. 552 (PDF 568), Theorem 11.4.2

import Definitions.Def_PutermanMDP_SemiMarkov_Stationary

namespace PutermanMDP.SemiMarkov

theorem evaluation_identifies_gain {S : Type*} [Countable S] [Nonempty S]
    (M : Model S) (d : Rule M) (hNE : Nonexplosive M)
    (hU : Unichain M d) (hP : CesaroProbability M d)
    (hE : FiniteEpochMoments M d)
    (g : ℝ) (h : S → ℝ) (hEq : EvaluationEquation M d (fun _ => g) h) :
    ∀ s, gain M d s = (g : EReal) := by sorry

end PutermanMDP.SemiMarkov
