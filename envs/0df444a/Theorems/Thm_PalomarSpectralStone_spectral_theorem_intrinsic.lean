-- Prove2me | Theorems.Thm_PalomarSpectralStone_spectral_theorem_intrinsic
-- name    : PalomarSpectralStone.spectral_theorem_intrinsic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:17:56.577516+00:00
-- url     : https://prove2.me/theorems/cbdddbbb-9bee-57c7-963e-046cfd87a920
-- title:
--   Palomar Spectral Stone: spectral theorem intrinsic
-- statement:
--   Every unbounded self-adjoint operator has a real PVM spectral
--   representation, unique on Borel-measurable sets.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L74-L83
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L74-L83

import Definitions.Def_Spectral_Spectral_Intrinsic
import Definitions.Def_Spectral_Stone_Intrinsic
import Definitions.Def_SpectralStoneSolution
import Theorems.Thm_spectral_theorem_intrinsic

set_option autoImplicit false
open Function MeasureTheory
open PalomarSpectralStone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PalomarSpectralStone.spectral_theorem_intrinsic
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ E_pvm : PVM E,
      E_pvm.Represents A ∧
      ∀ F_pvm : PVM E, F_pvm.Represents A →
        ∀ S : Set ℝ, MeasurableSet S → E_pvm.proj S = F_pvm.proj S := by sorry
