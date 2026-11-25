-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_wd_congr
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.Inv.wd_congr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:50:23.683485+00:00
-- url     : https://prove2.me/theorems/52ff7bfc-a3d8-4af0-a1b7-de93eb243af3
-- title:
--   Inv: wd congr
-- statement:
--   The Inv construction uses the wd congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L44-L48

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv

theorem PositivityTheory.Rg.Sw.WR.K.GB.Inv.wd_congr {f g : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (h : ∀ y ∈ U, f y = g y)
    (L : List (Mc n)) : ∀ x ∈ U, wd L f x = wd L g x := by sorry
