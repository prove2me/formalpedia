-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_two_sided_bs_nonunique
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.two_sided_bs_nonunique
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:34:31.860624+00:00
-- url     : https://prove2.me/theorems/59413ee7-1839-4b06-809f-7b2b9a715b55
-- title:
--   §8.3 unnumbered: two-sided BS form is nonunique
-- statement:
--   Consider the two-sided Bocharov–Svore syntax
--
--   $$
--   C_L\bigl(\varepsilon\mid TH\mid(TH)^2\mid(TH)^3\mid(TH)^4(TH\mid SHTH)^*\bigr)C_R,
--   $$
--   with operator-valued Clifford factors on both sides. There are two explicit pairs of distinct forms with equal absolute matrices:
--
--   $$
--   Z.TH=TH.X,\qquad YS.TH.TH=TH.TH.X\omega.
--   $$
--   Here $\omega$ on the right is the scalar $\omega I$. The dot delimits syllables only. Both pairs are concrete valid expressions of the two-sided syntax, so the observation establishes nonuniqueness without relying on an external existence result.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 12, §8.3 unnumbered: two-sided BS form is nonunique

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Section 8.3 after (25), PDF p.12: BOTH distinct two-sided BS witness pairs:
Z.TH = TH.X and YS.TH.TH = TH.TH.Xomega, with absolute phase preserved. -/
theorem two_sided_bs_nonunique :
    twoSidedBSWitness 0 ≠ twoSidedBSWitness 1 ∧
    twoSidedBSValue (twoSidedBSWitness 0) = twoSidedBSValue (twoSidedBSWitness 1) ∧
    twoSidedBSWitness 2 ≠ twoSidedBSWitness 3 ∧
    twoSidedBSValue (twoSidedBSWitness 2) = twoSidedBSValue (twoSidedBSWitness 3) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
