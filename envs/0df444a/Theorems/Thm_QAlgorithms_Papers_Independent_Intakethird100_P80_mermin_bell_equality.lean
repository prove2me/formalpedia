-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_mermin_bell_equality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.mermin_bell_equality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:26:49.380207+00:00
-- url     : https://prove2.me/theorems/c0a94311-574b-45d7-b97b-99b49d152e82
-- title:
--   Optimized Mermin equals optimized Bell
-- statement:
--   For the fixed Mermin and optimized Bell experiments of Appendix III, their optimized strengths agree both when settings must be independent and when correlations are allowed:
--
--   $$S^{\rm UC}_{\rm Mermin}=S^{\rm UC}_{\rm Bell\ optimized},\qquad S^{\rm COR}_{\rm Mermin}=S^{\rm COR}_{\rm Bell\ optimized}.$$
--
--   This is the equality for non-uniform optimized sampling described in Section V. It does not identify their distinct uniform strengths or certify rounded optimizer entries at unused settings.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 9, Section V: optimized Mermin equals optimized Bell strength

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

/-- PDF p.9, Section V (Tables XXIV–XXVII, p.23): Mermin and optimized Bell have equal
optimized product and correlated strengths. Their UNIFORM strengths are not equated. -/
theorem mermin_bell_equality :
    uncorrelatedStrength mermin = uncorrelatedStrength optimizedBell ∧
    correlatedStrength mermin = correlatedStrength optimizedBell := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
