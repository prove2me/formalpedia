-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_iconst_mul
-- name    : PositivityTheory.Rg.Sw.LVs.CK.iconst_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:31.402089+00:00
-- url     : https://prove2.me/theorems/4ec7878b-fda8-4f72-a24a-01626020fa0a
-- title:
--   CK: iconst mul
-- statement:
--   The CK construction uses the iconst mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDeterminantPowerZeroInt.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDeterminantPowerZeroInt.lean#L34-L39

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerCornerInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt
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

theorem PositivityTheory.Rg.Sw.LVs.CK.iconst_mul {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (G : F → ℂ) (x : F) (a : ℂ)
    (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin n → F) :
    iteratedFDeriv ℂ n (fun y => a * G y) x u = a * iteratedFDeriv ℂ n G x u := by sorry
