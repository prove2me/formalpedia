-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_psa_symm_self
-- name    : PositivityTheory.Rg.BcB.CG.psa_symm_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:13.56295+00:00
-- url     : https://prove2.me/theorems/96040476-1a67-45c8-9b3b-dccd979a3e7b
-- title:
--   CG: psa symm self
-- statement:
--   The CG construction uses the psa symm self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L64-L66

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
variable {Idx : ι → Type}

theorem PositivityTheory.Rg.BcB.CG.psa_symm_self (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) :
    (Equiv.piSplitAt w Idx).symm (j, J') w = j := by sorry
