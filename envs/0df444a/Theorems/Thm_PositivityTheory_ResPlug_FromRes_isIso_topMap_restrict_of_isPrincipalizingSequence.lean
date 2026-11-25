-- Prove2me | Theorems.Thm_PositivityTheory_ResPlug_FromRes_isIso_topMap_restrict_of_isPrincipalizingSequence
-- name    : PositivityTheory.ResPlug.FromRes.isIso_topMap_restrict_of_isPrincipalizingSequence
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:50:44.266111+00:00
-- url     : https://prove2.me/theorems/7456385b-07c7-5284-8d26-46795676bbf7
-- title:
--   From Res: is Iso top Map restrict of is Principalizing Sequence
-- statement:
--   The From Res construction uses the is Iso top Map restrict of is Principalizing Sequence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResIso.lean#L24-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ResolutionCharZero/FromResIso.lean#L24-L77

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Statements
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_WeilBound_CoreStatements_ResolutionCharZero_FromResIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open PositivityTheory PositivityTheory.ResPlug PositivityTheory.ResPlug.FromRes
open FunctorialResolution

theorem PositivityTheory.ResPlug.FromRes.isIso_topMap_restrict_of_isPrincipalizingSequence {k : Type} [Field k] {X : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {E : List X.IdealSheafData} {s : BlowupSequence X}
    (h : IsPrincipalizingSequence p I E s) : IsIso (s.topMap ∣_ I.support.compl) := by sorry
