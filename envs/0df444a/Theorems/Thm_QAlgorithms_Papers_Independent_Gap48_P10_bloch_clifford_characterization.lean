-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_bloch_clifford_characterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.bloch_clifford_characterization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:20:59.024045+00:00
-- url     : https://prove2.me/theorems/5eada004-28a7-4c18-8852-c53b7d0f12dd
-- title:
--   Remark 4.2: Bloch Clifford characterization
-- statement:
--   Write $\widehat U$ for the Bloch matrix determined in ordered $X,Y,Z$ coordinates by conjugation $A\mapsto UAU^\dagger$, and let $\widehat{\mathcal C}$ be the image of the exact Clifford group. Then
--
--   $$
--   |\widehat{\mathcal C}|=24,\qquad
--   \widehat{\mathcal C}=\{R\in SO(3):R_{ij}\in\{-1,0,1\}\}
--   =\{R\in SO(3):R(Q)=Q\},
--   $$
--   where $Q=\{x\in\mathbb R^3:-1\le x_i\le1\text{ for all }i\}$. Here $SO(3)$ means real orthogonal $3\times3$ matrices of determinant one.
--
--   The characterization concerns rotational cube symmetries; reflections are excluded by determinant one.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 3, Remark 4.2: Bloch Clifford characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Remark 4.2, PDF p.3. The Bloch Clifford group consists of 24 signed permutation
rotations and is exactly the rotation group preserving the displayed cube. -/
theorem bloch_clifford_characterization :
    Nat.card {V : RealMat // ∃ C : Clifford, operatorBloch C.val = V} = 24 ∧
    ∀ U : RealMat,
      ((∃ C : Clifford, operatorBloch C.val = U) ↔
        SpecialOrthogonal U ∧ ∀ i j, U i j = -1 ∨ U i j = 0 ∨ U i j = 1) ∧
      ((∃ C : Clifford, operatorBloch C.val = U) ↔
        SpecialOrthogonal U ∧ Set.image (fun x => U.mulVec x) cube = cube) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
