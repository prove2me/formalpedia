-- Prove2me | Theorems.Thm_StatComplexityDM_Estimation_hellinger_estimation_le_logloss_regret
-- name    : StatComplexityDM.Estimation.hellinger_estimation_le_logloss_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:20.909695+00:00
-- url     : https://prove2.me/theorems/35662b0d-eb04-428d-92a1-4277c78089e6
-- title:
--   Lemma A.14 (102), p. 76 — high-probability Hellinger estimation error bound
-- statement:
--   In a realizable online conditional density process with true expert $i^\star$, any learner and adaptive covariate process satisfy, for every $\delta\in(0,1)$ and with probability at least $1-\delta$,
--   $$
--   \mathrm{Est}_{\mathrm H}\le \mathrm{Reg}_{\mathrm{KL}}+2\log(1/\delta).
--   $$
--   The Hellinger error sums conditional expected squared distances, averaging the next covariate under its history-dependent law. Regret is the learner's realized cumulative log loss minus the best expert's realized cumulative log loss.
--
--   This turns log-loss regret into a high-probability estimation guarantee used in the paper's decision bounds.
--
--   **Formalization Note** Covariates, outcomes, and experts are finite; the true outcome law is built into the history law as Assumption A.1. Rounds are 0-based. The learner and every expert must assign positive density to observed outcomes on positive-probability histories so real log loss agrees with the paper's extended log loss. The failure event has mass at most $\delta$.
-- source:
--   arXiv:2112.13487v3, Lemma A.14, (102), p. 76; proof pp. 78–79

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_Estimation_Sequential
import Definitions.Def_StatComplexityDM_Estimation_Process

namespace StatComplexityDM.Estimation

open Classical

/-- Lemma A.14 (102), p. 76: log-loss regret controls conditional Hellinger estimation
error with probability at least `1 - δ`. -/
theorem hellinger_estimation_le_logloss_regret
    {I X Y : Type*} [Fintype I] [Nonempty I] [Fintype X] [Fintype Y] {T : ℕ}
    (ctx : ContextKernel X Y T) (ghat : Predictor X Y T)
    (g : Experts I X Y T) (istar : I)
    (hctx : IsContextKernel ctx) (hghat : IsPredictor ghat)
    (hg : IsExperts g) (hpos : PositiveOnSupport ctx ghat g istar)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    (∑ h : Hist (X × Y) T,
      if regKL ghat g h + 2 * Real.log (1 / δ) < estH ctx ghat g istar h
      then law ctx g istar h else 0) ≤ δ := by sorry

end StatComplexityDM.Estimation
