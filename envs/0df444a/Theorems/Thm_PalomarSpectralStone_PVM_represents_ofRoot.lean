-- Prove2me | Theorems.Thm_PalomarSpectralStone_PVM_represents_ofRoot
-- name    : PalomarSpectralStone.PVM.represents_ofRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:13:15.506049+00:00
-- url     : https://prove2.me/theorems/8b607677-edd3-45a6-858f-800af257ca78
-- title:
--   PVM: represents of Root
-- statement:
--   The PVM construction uses the represents of Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L66-L67
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean#L66-L67

import Definitions.Def_Spectral_Spectral_Intrinsic
import Definitions.Def_Spectral_Stone_Intrinsic
import Definitions.Def_SpectralStoneSolution
set_option autoImplicit false
open Function MeasureTheory
open PalomarSpectralStone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PalomarSpectralStone.PVM.represents_ofRoot {p : _root_.PVM E} {A : E →ₗ.[ℂ] E} :
    (PVM.ofRoot p).Represents A ↔ p.Represents A := by sorry
