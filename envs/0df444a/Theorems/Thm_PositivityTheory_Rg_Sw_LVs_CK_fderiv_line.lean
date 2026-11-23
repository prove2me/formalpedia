-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_fderiv_line
-- name    : PositivityTheory.Rg.Sw.LVs.CK.fderiv_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:05.834927+00:00
-- url     : https://prove2.me/theorems/19f45c11-57e9-4cc1-ace6-4ed3d7cad69a
-- title:
--   CK: fderiv line
-- statement:
--   The CK construction uses the fderiv line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerCornerInt.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerCornerInt.lean#L15-L21

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetColumnPerturbation
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerCornerInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {N : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.CK.fderiv_line {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (G : F → ℂ) (y v : F)
    (hG : DifferentiableAt ℂ G y) : HasDerivAt (fun s : ℂ => G (y + s • v)) (fderiv ℂ G y v) 0 := by sorry
