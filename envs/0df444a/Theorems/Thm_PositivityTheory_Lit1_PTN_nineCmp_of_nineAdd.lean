-- Prove2me | Theorems.Thm_PositivityTheory_Lit1_PTN_nineCmp_of_nineAdd
-- name    : PositivityTheory.Lit1.PTN.nineCmp_of_nineAdd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:51.665278+00:00
-- url     : https://prove2.me/theorems/1c03c46d-6eb2-582f-8f1f-394122e02d0c
-- title:
--   PTN: nine Cmp of nine Add
-- statement:
--   The PTN construction uses the nine Cmp of nine Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoitouTateDuality/PtfsNineAdd.lean#L27-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoitouTateDuality/PtfsNineAdd.lean#L27-L42

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsDefs
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsAddTransfer
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsNineAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion
open PositivityTheory PositivityTheory.Lit1 PositivityTheory.Lit1.PTN

theorem PositivityTheory.Lit1.PTN.nineCmp_of_nineAdd {N : ℕ} {A0 A1 A2 A3 A4 A5 A6 A7 A8 : Type} [AddCommGroup A0] [Module (ZMod N) A0] [AddCommGroup A1] [Module (ZMod N) A1] [AddCommGroup A2] [Module (ZMod N) A2] [AddCommGroup A3] [Module (ZMod N) A3] [AddCommGroup A4] [Module (ZMod N) A4] [AddCommGroup A5] [Module (ZMod N) A5] [AddCommGroup A6] [Module (ZMod N) A6] [AddCommGroup A7] [Module (ZMod N) A7] [AddCommGroup A8] [Module (ZMod N) A8]
    {f0 : A0 →ₗ[ZMod N] A1} {f1 : A1 →ₗ[ZMod N] A2} {f3 : A3 →ₗ[ZMod N] A4}
    {f4 : A4 →ₗ[ZMod N] A5} {f6 : A6 →ₗ[ZMod N] A7} {f7 : A7 →ₗ[ZMod N] A8}
    (h : NineAdd f0 f1 f3 f4 f6 f7) : NineCmp f0 f1 f3 f4 f6 f7 := by sorry
