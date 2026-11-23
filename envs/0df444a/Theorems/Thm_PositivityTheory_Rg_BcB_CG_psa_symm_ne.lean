-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_psa_symm_ne
-- name    : PositivityTheory.Rg.BcB.CG.psa_symm_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:55.435796+00:00
-- url     : https://prove2.me/theorems/43615a38-da4a-4a2f-b629-433430f1452b
-- title:
--   CG: psa symm ne
-- statement:
--   The CG construction uses the psa symm ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L68-L70

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

theorem PositivityTheory.Rg.BcB.CG.psa_symm_ne (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) (v : {v // v ≠ w}) :
    (Equiv.piSplitAt w Idx).symm (j, J') v = J' v := by sorry
