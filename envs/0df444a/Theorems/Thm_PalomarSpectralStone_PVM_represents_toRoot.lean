-- Prove2me | Theorems.Thm_PalomarSpectralStone_PVM_represents_toRoot
-- name    : PalomarSpectralStone.PVM.represents_toRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:14:22.380434+00:00
-- url     : https://prove2.me/theorems/3506494f-a798-4996-ab40-3c93ec85cbab
-- title:
--   PVM: represents to Root
-- statement:
--   The PVM construction uses the represents to Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L69-L70
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L69-L70

import Definitions.Def_Spectral_Spectral_Intrinsic
import Definitions.Def_Spectral_Stone_Intrinsic
import Definitions.Def_SpectralStoneSolution
set_option autoImplicit false
open Function MeasureTheory
open PalomarSpectralStone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PalomarSpectralStone.PVM.represents_toRoot {p : PVM E} {A : E →ₗ.[ℂ] E} :
    (PVM.toRoot p).Represents A ↔ p.Represents A := by sorry
