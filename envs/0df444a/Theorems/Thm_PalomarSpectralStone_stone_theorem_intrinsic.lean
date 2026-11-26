-- Prove2me | Theorems.Thm_PalomarSpectralStone_stone_theorem_intrinsic
-- name    : PalomarSpectralStone.stone_theorem_intrinsic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:14:19.44219+00:00
-- url     : https://prove2.me/theorems/5666145a-917f-590d-a899-20ea3a127b57
-- title:
--   Palomar Spectral Stone: stone theorem intrinsic
-- statement:
--   Stone's theorem: every strongly continuous unitary group has a
--   self-adjoint generator, and every self-adjoint operator generates such
--   a group.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L125-L134
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L125-L134

import Definitions.Def_Spectral_Spectral_Intrinsic
import Definitions.Def_Spectral_Stone_Intrinsic
import Definitions.Def_SpectralStoneSolution
import Theorems.Thm_stone_theorem_intrinsic

set_option autoImplicit false
open Function MeasureTheory
open PalomarSpectralStone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PalomarSpectralStone.stone_theorem_intrinsic :
    (∀ U : StrongContUnitary E, ∃ A : E →ₗ.[ℂ] E,
      IsSelfAdjoint A ∧ U.Generates A) ∧
    (∀ A : E →ₗ.[ℂ] E, IsSelfAdjoint A →
      ∃ U : StrongContUnitary E, U.Generates A) := by sorry
