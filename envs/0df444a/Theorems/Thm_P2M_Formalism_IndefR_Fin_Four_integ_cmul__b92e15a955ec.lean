-- Prove2me | Theorems.Thm_P2M_Formalism_IndefR_Fin_Four_integ_cmul__b92e15a955ec
-- name    : P2M_Formalism_IndefR_Fin_Four_integ_cmul__b92e15a955ec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:31.361938+00:00
-- url     : https://prove2.me/theorems/a6200eca-aeec-4d18-bd07-75d3bebc68e5
-- title:
--   P2 M Formalism Indef R Fin Four integ cmul  b92e15a955ec: P2 M Formalism Indef R Fin Four integ cmul  b92e15a955ec
-- statement:
--   The P2 M Formalism Indef R Fin Four integ cmul  b92e15a955ec construction uses the P2 M Formalism Indef R Fin Four integ cmul  b92e15a955ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L199-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L199-L214

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Finset
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W : Type*} [AddCommGroup W]
variable {H : AddSubgroup W} (hfin : ∀ k, 0 < k → Finite (Qt k H))
include hfin

theorem P2M_Formalism_IndefR_Fin_Four_integ_cmul__b92e15a955ec (g : W → ℂ) (c : ℂ) : integ H (fun t => c * g t) = c * integ H g := by sorry

alias «Formalism».«IndefR».«Fin».«Four».«integ_cmul'» := P2M_Formalism_IndefR_Fin_Four_integ_cmul__b92e15a955ec
