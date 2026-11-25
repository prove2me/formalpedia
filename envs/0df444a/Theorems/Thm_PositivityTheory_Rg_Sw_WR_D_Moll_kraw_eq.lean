-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_kraw_eq
-- name    : PositivityTheory.Rg.Sw.WR.D.Moll.kraw_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:05:14.794651+00:00
-- url     : https://prove2.me/theorems/eb44fc28-0024-5a00-9c36-d3a35d49fae7
-- title:
--   Moll: kraw eq
-- statement:
--   The Moll construction uses the kraw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/MollIdA.lean#L74-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/MollIdA.lean#L74-L156

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.D.Moll.kraw_eq (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ≠ 0) (u : E n) :
    (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      (((|t| / (2 * Real.sqrt ε)) ^ (n ^ 2) * gK ((|t| / (2 * Real.sqrt ε)) • u) : ℝ) : ℂ) := by sorry
