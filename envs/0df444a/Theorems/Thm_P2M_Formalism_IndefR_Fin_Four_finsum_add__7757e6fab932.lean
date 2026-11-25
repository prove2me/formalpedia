-- Prove2me | Theorems.Thm_P2M_Formalism_IndefR_Fin_Four_finsum_add__7757e6fab932
-- name    : P2M_Formalism_IndefR_Fin_Four_finsum_add__7757e6fab932
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:32.256003+00:00
-- url     : https://prove2.me/theorems/0d5a0de3-acfa-424b-b691-3550efd36f94
-- title:
--   P2 M Formalism Indef R Fin Four finsum add  7757e6fab932: P2 M Formalism Indef R Fin Four finsum add  7757e6fab932
-- statement:
--   The P2 M Formalism Indef R Fin Four finsum add  7757e6fab932 construction uses the P2 M Formalism Indef R Fin Four finsum add  7757e6fab932 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulFinsum.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulFinsum.lean#L13-L15

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {α M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

theorem P2M_Formalism_IndefR_Fin_Four_finsum_add__7757e6fab932 {f g : α → M} (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    ∑ᶠ i, (f i + g i) = ∑ᶠ i, f i + ∑ᶠ i, g i := by sorry

alias «Formalism».«IndefR».«Fin».«Four».«finsum_add'» := P2M_Formalism_IndefR_Fin_Four_finsum_add__7757e6fab932
