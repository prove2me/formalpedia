-- Prove2me | Theorems.Thm_P2M_Formalism_IndefR_Fin_Four_smul_finsum__d1458f58bfdd
-- name    : P2M_Formalism_IndefR_Fin_Four_smul_finsum__d1458f58bfdd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:37.704945+00:00
-- url     : https://prove2.me/theorems/c1e32eb8-fd78-4d73-9080-be62e2af6aed
-- title:
--   P2 M Formalism Indef R Fin Four smul finsum  d1458f58bfdd: P2 M Formalism Indef R Fin Four smul finsum  d1458f58bfdd
-- statement:
--   The P2 M Formalism Indef R Fin Four smul finsum  d1458f58bfdd construction uses the P2 M Formalism Indef R Fin Four smul finsum  d1458f58bfdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulFinsum.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulFinsum.lean#L21-L23

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

theorem P2M_Formalism_IndefR_Fin_Four_smul_finsum__d1458f58bfdd (c : ℂ) {f : α → M} (hf : (Function.support f).Finite) :
    c • ∑ᶠ i, f i = ∑ᶠ i, c • f i := by sorry

alias «Formalism».«IndefR».«Fin».«Four».«smul_finsum'» := P2M_Formalism_IndefR_Fin_Four_smul_finsum__d1458f58bfdd
