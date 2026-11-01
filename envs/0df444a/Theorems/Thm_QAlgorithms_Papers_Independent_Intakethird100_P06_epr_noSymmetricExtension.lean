-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P06_epr_noSymmetricExtension
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P06.epr_noSymmetricExtension
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:03:35.766884+00:00
-- url     : https://prove2.me/theorems/0b8a40e2-c9f1-436c-90fd-f98ab0131985
-- title:
--   The EPR pair has no symmetric three-party extension
-- statement:
--   Let $\Phi=(|00\rangle+|11\rangle)/\sqrt{2}$ and let $P_\Phi=|\Phi\rangle\langle\Phi|$. Alice, Bob and Joe each have one qubit. There is no normalized positive three-qubit density operator $\omega$ satisfying either of the following two sets of requirements:
--
--   $$
--   \operatorname{Tr}_J\omega=P_\Phi,\qquad S_{BJ}\omega S_{BJ}^{\dagger}=\omega;
--   $$
--
--   $$
--   \operatorname{Tr}_J\omega=P_\Phi,\qquad \operatorname{Tr}_B\omega=P_\Phi.
--   $$
--
--   Here $S_{BJ}$ interchanges Bob and Joe while fixing Alice; in the second display the surviving spaces are identified in the order Alice, Joe. No purity assumption is imposed on $\omega$.
--
--   This states the impossibility of both the strong symmetric extension and the equal-marginal extension of the ideal EPR pair.
-- source:
--   Is Entanglement Monogamous?, arXiv:quant-ph/0307120v1, PDF p. 5, Section II, unnumbered: the EPR pair has no symmetric three-party extension

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P06

open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion)

open QAlgorithms.Papers.Independent.Frontier18.P09 (partialTraceRightCoeff)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section II, arXiv:quant-ph/0307120v1, PDF p.5 (weak terminology p.7):
the EPR marginal admits neither a Bob/Joe invariant three-qubit extension nor
one with equal EPR marginals on Alice-Bob and Alice-Joe. Global purity and
product factorization are not hypotheses. -/
theorem epr_noSymmetricExtension :
    (¬ ∃ omega : Matrix ((Opinion × Opinion) × Opinion)
        ((Opinion × Opinion) × Opinion) ℂ,
      IsCoordinateDensity omega ∧ traceRight omega = eprDensity ∧
        omega = swapBobJoe omega) ∧
    (¬ ∃ omega : Matrix ((Opinion × Opinion) × Opinion)
        ((Opinion × Opinion) × Opinion) ℂ,
      IsCoordinateDensity omega ∧ traceRight omega = eprDensity ∧
        aliceJoeMarginal omega = eprDensity) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P06

end
