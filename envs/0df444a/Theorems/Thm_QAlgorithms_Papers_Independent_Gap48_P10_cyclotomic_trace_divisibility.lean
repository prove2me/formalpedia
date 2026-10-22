-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_cyclotomic_trace_divisibility
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.cyclotomic_trace_divisibility
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:26:53.627327+00:00
-- url     : https://prove2.me/theorems/4b311b4b-0f4e-4a9c-a31d-c244bb3e690c
-- title:
--   Lemma 7.1: trace divisibility
-- statement:
--   Let $\omega=e^{i\pi/4}$ and $t\in\mathbb Z[\omega]$. There exists $q\in\mathbb Z[\omega]$ such that
--
--   $$
--   t+\overline t=\sqrt2\,q.
--   $$
--   Divisibility takes place in the cyclotomic integer ring, so the quotient is required to be a cyclotomic integer. This arithmetic constraint is used in the unit-vector residue exclusion.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 8, Lemma 7.1: trace divisibility

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Lemma 7.1, PDF p.8. The quotient belongs to Z[omega]; divisibility in the
ambient complex field would have no content. -/
theorem cyclotomic_trace_divisibility (t : ℂ) (ht : InZomega t) :
    ∃ q : ℂ, InZomega q ∧ t + star t = ((Real.sqrt 2 : ℝ) : ℂ) * q := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
