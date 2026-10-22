-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_directLink
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.directLink
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:48:00.804618+00:00
-- url     : https://prove2.me/theorems/dbf3724b-bbe0-422d-b742-616f929593be
-- title:
--   Appendix B.2.b: direct pair-link rate, Eq.(B1)
-- statement:
--   In Appendix B's perfect-pair, noiseless-channel toy model, let $\nu_S>0$ be the source clock, $t\in[0,1]$ total pair propagation transmission and $0<\eta\le1$ each endpoint detector's efficiency. Dark counts, dead times and other nuisances are absent. The independent propagation and two detection factors define a nonnegative normalized round law. Its coincidence rate, equal to the toy model's noiseless secret-key rate, is
--
--   $$K_1=R_1=\nu_St\eta^2.$$
--
--   The channel factor is the total path transmission $t$, whereas the two endpoint detections contribute $\eta^2$. In particular zero propagation transmission gives zero rate.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 46, Appendix B.2.b: direct pair-link rate, Eq.(B1)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eq.(B1), PDF p.46: direct-link coincidence rate, with eta^2 and total loss t. -/
theorem directLink (nu t eta : ℝ) (hnu : 0 < nu) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heta : 0 < eta ∧ eta ≤ 1) :
    (∀ b, 0 ≤ directLaw t eta b) ∧ (∑ b : Fin 3 → Bool, directLaw t eta b) = 1 ∧
    directRate nu t eta = nu*t*eta^2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
