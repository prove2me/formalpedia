-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_rational_single_run_program
-- name    : StableMSR.Recovery.Supplement.rational_single_run_program
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-19T01:00:52.794581+00:00
-- url     : https://prove2.me/theorems/d8c30720-a01c-479d-9872-06a7b7e14570
-- title:
--   One randomized recovery trial at fixed rational slack
-- statement:
--   For each fixed rational slack $0<e<1$, there is one finite admissible distance-table RAM program, chosen before the instance, with common absolute positive constants $a,b$. On every finite metric and valid exact cluster count, every tape yields a feasible output within $T=a n^{bE(e)}$ charged steps. If the input is $(1+e)$-stable, the probability that this single run's output differs from the optimum is at most $2/3$. This is the machine implementation obligation for the rational parameter case of Theorem 4.5. Rational approximation of an arbitrary stability factor, conversion to the inverse-fifth exponent, and amplification over independent runs are handled separately.
-- source:
--   https://arxiv.org/abs/2611.03547

import Definitions.Def_StableMSR_Recovery_Supplement_RandomExecution

set_option autoImplicit false
open scoped Classical ENNReal

namespace StableMSR.Recovery.Supplement

/-- A single fixed-rational-parameter trial on the public distance-table RAM. -/
theorem rational_single_run_program :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∀ e : ℚ, 0 < e → e < 1 →
      ∃ P : MinSumFPT.Program, MinSumFPT.Admissible P ∧
        ∀ (n k : ℕ) (d : Point n → Point n → ℝ), 1 ≤ k → k ≤ n → IsMetricArray d →
          let T := a*n^(b*parameterEnvelope (e:ℝ))
          AlwaysFeasible P n k d T ∧ ∀ O : Partition n,
            Stable d k (1+(e:ℝ)) O →
            MinSumFPT.tapeLaw {ω | randomOutput P n k d T ω ≠ O} ≤ (2/3 : ENNReal) := by sorry

end StableMSR.Recovery.Supplement
