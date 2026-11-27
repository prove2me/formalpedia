-- Prove2me | Theorems.Thm_P2M_Formalism_FG_FormalGroupLawMap_map_subst__1d1b80fad526
-- name    : P2M_Formalism_FG_FormalGroupLawMap_map_subst__1d1b80fad526
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:10:22.441949+00:00
-- url     : https://prove2.me/theorems/db58fd99-5f0b-51ba-825f-4c74ea0c13ab
-- title:
--   P2 M Formalism FG Formal Group Law Map map subst  1d1b80fad526: P2 M Formalism FG Formal Group Law Map map subst  1d1b80fad526
-- statement:
--   The P2 M Formalism FG Formal Group Law Map map subst  1d1b80fad526 construction uses the P2 M Formalism FG Formal Group Law Map map subst  1d1b80fad526 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftAsm.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftAsm.lean#L21-L24

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftAsm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.FormalGroupLawMap
open MvPowerSeries
variable {R S : Type*} [CommRing R] [CommRing S]

theorem P2M_Formalism_FG_FormalGroupLawMap_map_subst__1d1b80fad526 {σ τ : Type*} [Finite σ] (h : R →+* S) {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    map h (subst a f) = subst (fun s => map h (a s)) (map h f) := by sorry

alias «Formalism».«FG».«FormalGroupLawMap».«map_subst'» := P2M_Formalism_FG_FormalGroupLawMap_map_subst__1d1b80fad526
