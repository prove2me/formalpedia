-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_rationalIffFiniteModule
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.rationalIffFiniteModule
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:24:12.062778+00:00
-- url     : https://prove2.me/theorems/e24f019b-ea90-454f-a7eb-3a7889935c81
-- title:
--   Rationality detected by a finite module with nonzero contraction
-- statement:
--   Let $R$ be an algebraically closed field with $2$ invertible, let $n\ge2$, and let $\Omega$ be admissible. Then
--
--   $$\Omega\text{ is rational}\quad\Longleftrightarrow\quad\exists\text{ a finite-dimensional }W_n^{\mathrm{aff}}(\Omega)\text{-module with nonzero }E_1\text{-action}.$$
--
--   Rationality refers to the formal series at infinity, equivalently its eventual scalar recurrence. The module in the conclusion need not be irreducible. This characterizes rational parameters by finite representations.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 51, Lemma 7.18

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Lemma 7.18, PDF pp.51--52. The finite-dimensional module is not assumed
simple. Its nonzero E_1 action is expressed in a finite basis. -/
theorem rationalIffFiniteModule (R : Type u) [Field R] [IsAlgClosed R]
    [Invertible (2 : R)] (omega : ℕ → R) (n : ℕ) (hn : 2 ≤ n)
    (ha : OmegaAdmissible omega) :
    RationalSequence omega ↔ HasFiniteModule (F := R) (affineE R omega n 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
