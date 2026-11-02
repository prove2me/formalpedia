-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P96_ring_phase_unitary
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P96.ring_phase_unitary
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T22:15:26.74663+00:00
-- url     : https://prove2.me/theorems/23a29674-94d7-478b-94b4-91068c43309b
-- title:
--   Unitarity of the phase matrix on finite rings
-- statement:
--   For every natural number extra, the nearest-neighbor phase matrix in the existing formalization on the ring of extra + 5 sites is unitary. This establishes one conjunct of the open watrous_nonclosure milestone, not the remaining unitarity, Watrous-representation, composition, or adjoint conjuncts.
-- source:
--   B. Schumacher and R. F. Werner, Reversible Quantum Cellular Automata, arXiv:quant-ph/0405174v1, Sections IV.G and V.B, PDF pp. 12 and 14, https://arxiv.org/abs/quant-ph/0405174. The exact finite-ring theorem and extra + 5 encoding are those of the existing platform formalization; this is not a verbatim quotation of the paper.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P96

/-- The nearest-neighbor phase matrix is unitary on every ring in the model. -/
theorem ring_phase_unitary (extra : ℕ) :
    ringPhase extra ∈ Matrix.unitaryGroup (RingConfiguration extra) ℂ := by
  sorry

end QAlgorithms.Papers.Independent.Intakethird100.P96

end
