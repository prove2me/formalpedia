-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_Glob_VacS_gauss_scalar
-- name    : PositivityTheory.Rg.Sw.Glob.VacS.gauss_scalar
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:31.887869+00:00
-- url     : https://prove2.me/theorems/4f162030-5308-5e60-a8bd-b1bdf73e0604
-- title:
--   Vac S: gauss scalar
-- statement:
--   The Vac S construction uses the gauss scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/GaussScalar.lean#L9-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/GaussScalar.lean#L9-L32

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_GaussScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS

theorem PositivityTheory.Rg.Sw.Glob.VacS.gauss_scalar (b : ℂ) (hb : 0 < b.re) (s : ℝ) (w : ℂ) :
    ∫ y : ℂ, cexp (-b * ((‖y‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ w) * y).re : ℂ)) =
      ((Real.pi : ℂ) / b) * cexp (-((s : ℂ) ^ 2) * ((‖w‖ ^ 2 : ℝ) : ℂ) / b) := by sorry
