-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P96_ring_phase_hadamard_not_watrous
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P96.ring_phase_hadamard_not_watrous
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T22:06:31.667108+00:00
-- url     : https://prove2.me/theorems/4113de81-add3-4975-8068-0d7dab74a0d7
-- title:
--   The phase-after-Hadamard matrix is not of Watrous form on finite rings
-- statement:
--   For every natural number extra, consider the ring with extra + 5 sites and the existing formalization's sitewise Hadamard and nearest-neighbor phase matrices. Their product ringPhase extra * ringHadamard extra does not have the Watrous product representation defined by IsWatrous, even when that representation may use the entire ring as its neighborhood. This is one conjunct of the existing open watrous_nonclosure milestone; it does not establish the other conjuncts.
-- source:
--   B. Schumacher and R. F. Werner, Reversible Quantum Cellular Automata, arXiv:quant-ph/0405174v1, Section V.B, PDF pp. 14–15, https://arxiv.org/abs/quant-ph/0405174. This finite-ring statement isolates the exact non-Watrous conjunct of the existing formal milestone; the particular ring-length encoding and phase angle are part of that formalization.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P96

/-- The phase-after-Hadamard matrix is not of Watrous form on a ring of length at least five. -/
theorem ring_phase_hadamard_not_watrous (extra : ℕ) :
    ¬ IsWatrous extra (ringPhase extra * ringHadamard extra) := by
  sorry

end QAlgorithms.Papers.Independent.Intakethird100.P96

end
