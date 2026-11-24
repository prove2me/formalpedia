-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_CP_cay_inU
-- name    : PositivityTheory.SiegelWeilFormula.Krd.CP.cay_inU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:29.367128+00:00
-- url     : https://prove2.me/theorems/1e695b2e-75f0-418b-abf7-88272b8091b4
-- title:
--   CP: cay in U
-- statement:
--   The CP construction uses the cay in U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseCP.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseCP.lean#L11-L30

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

theorem PositivityTheory.SiegelWeilFormula.Krd.CP.cay_inU {J Y : Matrix ι ι ℂ} (hY : Yᴴ * J + J * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹)ᴴ * J * ((1 + Y) * (1 - Y)⁻¹) = J := by sorry
