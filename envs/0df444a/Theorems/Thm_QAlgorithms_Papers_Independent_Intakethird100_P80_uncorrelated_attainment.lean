-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_uncorrelated_attainment
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.uncorrelated_attainment
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:23:17.42003+00:00
-- url     : https://prove2.me/theorems/10aa3b07-9709-4ab0-ae3f-751b19cd174c
-- title:
--   A full-support optimal product setting law exists
-- statement:
--   Fix a $2\times2\times2$ quantum experiment $Q$; properness is not required. Let $\Sigma_{\rm UC}$ be the product setting laws and $u(\sigma)=\inf_{\pi\in\Pi}D_2(Q_\sigma\|P_{\sigma;\pi})$. There exists $\sigma^*\in\Sigma_{\rm UC}$ with every joint setting having positive probability such that
--
--   $$u(\sigma^*)=\sup_{\sigma\in\Sigma_{\rm UC}}u(\sigma).$$
--
--   Thus an optimal independent sampling design exists with full support even when the experiment is local.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 12, Unnumbered consequence of Theorem 1: optimal product settings exist

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

/-- PDF p.12, final sentence: a full-support PRODUCT maximizer exists, also for improper Q. -/
theorem uncorrelated_attainment {S : BellExperiment} (hS : TwoByTwo S)
    (hbinary : ∀ i a, S.outcomes i a = 2) (Q : Table S) (hQ : NonlocalityProof Q) :
    ∃ s : Sigma S, Uncorrelated s.1 ∧ PositiveCoordinates s.1 ∧
      lowerValue Q s.1 = uncorrelatedStrength Q := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
