-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_continuous_proj
-- name    : PositivityTheory.SiegelWeilFormula.Krd.DC.continuous_proj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:03:48.843907+00:00
-- url     : https://prove2.me/theorems/7d6e4aa7-0869-4282-a70c-09e6847974c6
-- title:
--   DC: continuous proj
-- statement:
--   The DC construction uses the continuous proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseC.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseC.lean#L74-L78

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DC
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PositivityTheory.SiegelWeilFormula.Krd.DC.continuous_proj (J : Matrix ι ι ℂ) (d : ℂ) : Continuous (proj J d) := by sorry
