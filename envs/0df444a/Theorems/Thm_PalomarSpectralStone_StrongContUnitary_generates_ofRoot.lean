-- Prove2me | Theorems.Thm_PalomarSpectralStone_StrongContUnitary_generates_ofRoot
-- name    : PalomarSpectralStone.StrongContUnitary.generates_ofRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:13:38.224807+00:00
-- url     : https://prove2.me/theorems/73e9f6d7-784c-41cc-b700-e1de30827198
-- title:
--   Strong Cont Unitary: generates of Root
-- statement:
--   The Strong Cont Unitary construction uses the generates of Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L114-L116
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L114-L116

import Definitions.Def_Spectral_Spectral_Intrinsic
import Definitions.Def_Spectral_Stone_Intrinsic
import Definitions.Def_SpectralStoneSolution
set_option autoImplicit false
open Function MeasureTheory
open PalomarSpectralStone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PalomarSpectralStone.StrongContUnitary.generates_ofRoot
    {u : _root_.StrongContUnitary E} {A : E →ₗ.[ℂ] E} :
    (StrongContUnitary.ofRoot u).Generates A ↔ u.Generates A := by sorry
