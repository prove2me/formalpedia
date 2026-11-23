-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiL_apply
-- name    : PositivityTheory.Rg.Sw.LVs.CK.phiL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:26.406568+00:00
-- url     : https://prove2.me/theorems/d266589c-0490-4231-bd59-ca5224693555
-- title:
--   CK: phi L apply
-- statement:
--   The CK construction uses the phi L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetColumnPerturbation.lean#L41-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetColumnPerturbation.lean#L41-L41

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetDFin
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetColumnPerturbation
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

theorem PositivityTheory.Rg.Sw.LVs.CK.phiL_apply (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : phiL N X = phiF X := by sorry

attribute [defeq] PositivityTheory.Rg.Sw.LVs.CK.phiL_apply
