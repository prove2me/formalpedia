-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_original_bs_nonunique
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.original_bs_nonunique
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:33:28.91097+00:00
-- url     : https://prove2.me/theorems/d572a8a6-d1f2-4965-818b-182b421e9f8e
-- title:
--   §8.3 unnumbered: original BS form is nonunique
-- statement:
--   In the original Bocharov–Svore syntax $(H\mid\varepsilon)(TH\mid SHTH)^*C$, the following are two pairs of distinct syntactic forms representing equal absolute matrices:
--
--   $$
--   H.H=I,\qquad SHTH.Z=H.SHTH.
--   $$
--   A dot marks a boundary between syllables or a terminal and has no operator meaning. Both sides of both equalities are represented as concrete data in the original syntax, with operator-valued Clifford terminals.
--
--   Thus the original form is nonunique, with both source witnesses retained.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 12, §8.3 unnumbered: original BS form is nonunique

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Section 8.3 after (21), PDF p.12: BOTH explicit pairs of distinct original
BS forms with identical operators: H.H = I and SHTH.Z = H.SHTH. -/
theorem original_bs_nonunique :
    originalBSWitness 0 ≠ originalBSWitness 1 ∧
    originalBSValue (originalBSWitness 0) = originalBSValue (originalBSWitness 1) ∧
    originalBSWitness 2 ≠ originalBSWitness 3 ∧
    originalBSValue (originalBSWitness 2) = originalBSValue (originalBSWitness 3) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
