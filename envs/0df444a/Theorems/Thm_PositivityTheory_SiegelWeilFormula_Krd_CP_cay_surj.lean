-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_CP_cay_surj
-- name    : PositivityTheory.SiegelWeilFormula.Krd.CP.cay_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:19.121835+00:00
-- url     : https://prove2.me/theorems/d5a9ff33-6487-49c7-abc3-1408a878d5f6
-- title:
--   CP: cay surj
-- statement:
--   The CP construction uses the cay surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseCP.lean#L32-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseCP.lean#L32-L71

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.CP
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PositivityTheory.SiegelWeilFormula.Krd.CP.cay_surj {J h : Matrix ι ι ℂ} (hh : hᴴ * J * h = J) (hu : IsUnit (1 + h).det) :
    ∃ Y : Matrix ι ι ℂ, Yᴴ * J + J * Y = 0 ∧ IsUnit (1 - Y).det ∧ (1 + Y) * (1 - Y)⁻¹ = h := by sorry
