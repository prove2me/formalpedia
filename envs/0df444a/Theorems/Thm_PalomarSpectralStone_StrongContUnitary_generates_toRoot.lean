-- Prove2me | Theorems.Thm_PalomarSpectralStone_StrongContUnitary_generates_toRoot
-- name    : PalomarSpectralStone.StrongContUnitary.generates_toRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:13:24.339375+00:00
-- url     : https://prove2.me/theorems/88adafcb-5652-46c2-b1e0-6252260f4720
-- title:
--   Strong Cont Unitary: generates to Root
-- statement:
--   The Strong Cont Unitary construction uses the generates to Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L118-L120
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L118-L120

import Definitions.Def_Spectral_Spectral_Intrinsic
import Definitions.Def_Spectral_Stone_Intrinsic
import Definitions.Def_SpectralStoneSolution
set_option autoImplicit false
open Function MeasureTheory
open PalomarSpectralStone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PalomarSpectralStone.StrongContUnitary.generates_toRoot
    {u : StrongContUnitary E} {A : E →ₗ.[ℂ] E} :
    (StrongContUnitary.toRoot u).Generates A ↔ u.Generates A := by sorry
