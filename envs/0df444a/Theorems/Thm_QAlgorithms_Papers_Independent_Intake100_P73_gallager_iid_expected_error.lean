-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_gallager_iid_expected_error
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.gallager_iid_expected_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:58:48.957995+00:00
-- url     : https://prove2.me/theorems/379fbcda-ff4a-46bc-a35d-e839361dd851
-- title:
--   Gallager: expected maximum-likelihood random-code error
-- statement:
--   For every normalized discrete channel W, input law p, and positive integer N, draw N codewords independently from p and decode by maximum likelihood, using a fixed tie convention. The expected uniform-message error is at most inf over 0<=s<=1 of N^s times sum_y (sum_x p(x) W_x(y)^(1/(1+s)))^(1+s). This is the Gallager [7] ingredient explicitly quoted in the proof of Theorem 3, with N=ML.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 6, Gallager [7] random-coding reliability bound used in Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi PDF p.6, proof of Theorem 3, explicitly attributed to Gallager [7].
For N iid codewords, the actual maximum-likelihood decoder's expected average
error has the stated optimized moment bound. Take N=ML in that proof. -/
theorem gallager_iid_expected_error {X Y : Type*}
    (W : X → Y → ℝ≥0∞) (hW : IsDiscreteStochastic W) (p : PMF X)
    (N : ℕ) (hN : 0 < N) :
    iidExpectation p N (fun a => iidMaximumLikelihoodError W a hN) ≤
      sInf ((fun s : ℝ => (N : ℝ≥0∞) ^ s * phiMoment W p s) '' Set.Icc 0 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
