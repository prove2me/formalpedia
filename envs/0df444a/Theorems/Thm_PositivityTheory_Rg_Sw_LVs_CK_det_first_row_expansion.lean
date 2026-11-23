-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_det_first_row_expansion
-- name    : PositivityTheory.Rg.Sw.LVs.CK.det_first_row_expansion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:22.057821+00:00
-- url     : https://prove2.me/theorems/a075f526-dcde-47e4-afe0-ed308e08d37b
-- title:
--   CK: det first row expansion
-- statement:
--   The CK construction uses the det first row expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetColumnPerturbation.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetColumnPerturbation.lean#L59-L64

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

theorem PositivityTheory.Rg.Sw.LVs.CK.det_first_row_expansion (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (a : ℂ) (h : ∀ j, A 0 j = if j = 0 then a else 0) :
    A.det = a * (A.submatrix Fin.succ Fin.succ).det := by sorry
