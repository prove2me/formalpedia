-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_qualitative_ranking
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.qualitative_ranking
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:26:08.359206+00:00
-- url     : https://prove2.me/theorems/d1059e94-e569-44f3-8cc9-332a2ec10e77
-- title:
--   Strict qualitative ranking among the six fixed experiments
-- statement:
--   Let $S^{\rm UC}$ denote the statistical strength with independent setting sampling for the six fixed experiments specified in Appendix III, with their states and measurement choices held fixed. Then
--
--   $$\max\{S^{\rm UC}_{\rm Bell\ original},S^{\rm UC}_{\rm Bell\ optimized},S^{\rm UC}_{\rm Hardy},S^{\rm UC}_{\rm Mermin}\}<S^{\rm UC}_{\rm CHSH}<S^{\rm UC}_{\rm GHZ}.$$
--
--   CHSH achieves its product-setting optimum with uniform sampling. This is a comparison within these six experiments; it does not assert global optimality among all bipartite quantum experiments. The paragraph's defective numerical factor is separately recorded as a deferral.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 9, Section V: qualitative comparison within the six fixed experiments

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

/-- PDF pp.8–9, Section V: strict comparison ONLY among the six fixed experiments.
The defective quantitative factor in the same paragraph is separately deferred. -/
theorem qualitative_ranking :
    uncorrelatedStrength originalBell < uncorrelatedStrength chshTable ∧
    uncorrelatedStrength optimizedBell < uncorrelatedStrength chshTable ∧
    uncorrelatedStrength hardy < uncorrelatedStrength chshTable ∧
    uncorrelatedStrength mermin < uncorrelatedStrength chshTable ∧
    uncorrelatedStrength chshTable < uncorrelatedStrength ghzTable ∧
    uniformStrength chshTable = uncorrelatedStrength chshTable := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
