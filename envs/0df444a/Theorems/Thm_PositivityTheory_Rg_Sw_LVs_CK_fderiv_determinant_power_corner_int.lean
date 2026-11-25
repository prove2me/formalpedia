-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_fderiv_determinant_power_corner_int
-- name    : PositivityTheory.Rg.Sw.LVs.CK.fderiv_determinant_power_corner_int
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:18.516723+00:00
-- url     : https://prove2.me/theorems/e29f08ca-2d31-4c48-9044-1952537aad73
-- title:
--   CK: fderiv determinant power corner int
-- statement:
--   The CK construction uses the fderiv determinant power corner int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerCornerInt.lean#L34-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerCornerInt.lean#L34-L64

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

theorem PositivityTheory.Rg.Sw.LVs.CK.fderiv_determinant_power_corner_int (t : ℤ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ≠ 0) :
    fderiv ℂ (H (N + 1) t) (phiF X) (Matrix.single 0 0 1) = (t : ℂ) * H N t (piF X) := by sorry
