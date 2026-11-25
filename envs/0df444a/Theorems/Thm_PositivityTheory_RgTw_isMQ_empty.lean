-- Prove2me | Theorems.Thm_PositivityTheory_RgTw_isMQ_empty
-- name    : PositivityTheory.RgTw.isMQ_empty
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:53:28.704301+00:00
-- url     : https://prove2.me/theorems/48211258-92ef-5dd3-9e87-14f7a5e67ac2
-- title:
--   Rg Tw: is MQ empty
-- statement:
--   The Rg Tw construction uses the is MQ empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/DiscreteSeriesTopClasses/IsMQEmpty.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/DiscreteSeriesTopClasses/IsMQEmpty.lean#L20-L24

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_DiscreteSeriesTopClasses_IsMQEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix Filter Topology MeasureTheory
open PositivityTheory PositivityTheory.RgTw

theorem PositivityTheory.RgTw.isMQ_empty (R : Type) [CommRing R] [Algebra ℂ R] :
    IsMQ (ι := Empty) (R := R) Empty.elim Empty.elim (fun k => if k = 0 then 1 else 0) Empty.elim := by sorry
