-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_fderiv_fsum
-- name    : PositivityTheory.Rg.Sw.LVs.CK.fderiv_fsum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:49:45.803149+00:00
-- url     : https://prove2.me/theorems/27994751-21de-4a87-a719-c1023d224452
-- title:
--   CK: fderiv fsum
-- statement:
--   The CK construction uses the fderiv fsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivFsum.lean#L27-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivFsum.lean#L27-L45

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerColumnSum
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivFsum
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

theorem PositivityTheory.Rg.Sw.LVs.CK.fderiv_fsum (t : ℤ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (hy : (1 + piF y).det ≠ 0) :
    fderiv ℂ (fsum t c) y (Matrix.single k0 0 1) = -fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1) := by sorry
