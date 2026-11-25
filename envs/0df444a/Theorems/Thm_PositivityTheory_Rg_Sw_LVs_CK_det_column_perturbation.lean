-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_det_column_perturbation
-- name    : PositivityTheory.Rg.Sw.LVs.CK.det_column_perturbation
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:49:18.925831+00:00
-- url     : https://prove2.me/theorems/60df37a0-c5ff-47f5-a3b4-e46e241b44cf
-- title:
--   CK: det column perturbation
-- statement:
--   The CK construction uses the det column perturbation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetColumnPerturbation.lean#L78-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetColumnPerturbation.lean#L78-L105

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

theorem PositivityTheory.Rg.Sw.LVs.CK.det_column_perturbation (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) (c : Fin N) :
    (1 + phiF X + s • Matrix.single 0 c.succ 1).det = (1 + piF X - s • colQ X c).det := by sorry
