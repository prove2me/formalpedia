-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_WR_Ib_herm_apply__3d4eedff4794
-- name    : P2M_PositivityTheory_Rg_Sw_WR_Ib_herm_apply__3d4eedff4794
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:10:48.838268+00:00
-- url     : https://prove2.me/theorems/a83ff379-1b80-47e7-a718-f9ed26e02a1a
-- title:
--   P2 M Positivity Theory Rg Sw WR Ib herm apply  3d4eedff4794: P2 M Positivity Theory Rg Sw WR Ib herm apply  3d4eedff4794
-- statement:
--   The P2 M Positivity Theory Rg Sw WR Ib herm apply  3d4eedff4794 construction uses the P2 M Positivity Theory Rg Sw WR Ib herm apply  3d4eedff4794 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L68-L69

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_WR_Ib_herm_apply__3d4eedff4794 (x : E n) (i j : Fin n) :
    herm x i j = ((x i j + x j i : ℝ) : ℂ) / 2 + Complex.I * ((x i j - x j i : ℝ) : ℂ) / 2 := by sorry

alias «PositivityTheory».«Rg».«Sw».«WR».«Ib».«herm_apply'» := P2M_PositivityTheory_Rg_Sw_WR_Ib_herm_apply__3d4eedff4794
