-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_fderiv_determinant_power_column_sum
-- name    : PositivityTheory.Rg.Sw.LVs.CK.fderiv_determinant_power_column_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:49:26.951944+00:00
-- url     : https://prove2.me/theorems/22516b32-6783-4999-91e5-99b8aff36517
-- title:
--   CK: fderiv determinant power column sum
-- statement:
--   The CK construction uses the fderiv determinant power column sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerColumnSum.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerColumnSum.lean#L27-L30

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerColumnSum
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

theorem PositivityTheory.Rg.Sw.LVs.CK.fderiv_determinant_power_column_sum (t : ℤ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ≠ 0) (c : Fin N) :
    fderiv ℂ (H (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = fsum t c X := by sorry
