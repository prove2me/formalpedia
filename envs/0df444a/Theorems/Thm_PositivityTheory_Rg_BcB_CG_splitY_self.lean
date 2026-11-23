-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitY_self
-- name    : PositivityTheory.Rg.BcB.CG.splitY_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:11.840142+00:00
-- url     : https://prove2.me/theorems/b93a2025-7884-4665-b296-76741c9392e3
-- title:
--   CG: split Y self
-- statement:
--   The CG construction uses the split Y self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L15-L15

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG
variable {ι : Type} [DecidableEq ι] {X : Type}

theorem PositivityTheory.Rg.BcB.CG.splitY_self (w : ι) (t : X) (z : {v // v ≠ w} → X) : splitY w t z w = t := by sorry
