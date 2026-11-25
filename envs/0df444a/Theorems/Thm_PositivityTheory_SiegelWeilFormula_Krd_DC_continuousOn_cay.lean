-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_continuousOn_cay
-- name    : PositivityTheory.SiegelWeilFormula.Krd.DC.continuousOn_cay
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:03:40.160637+00:00
-- url     : https://prove2.me/theorems/e9fbb0ef-c6aa-54ef-ba0c-edf356df7dc7
-- title:
--   DC: continuous On cay
-- statement:
--   The DC construction uses the continuous On cay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseC.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseC.lean#L36-L46

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

theorem PositivityTheory.SiegelWeilFormula.Krd.DC.continuousOn_cay : ContinuousOn (cay (ι := ι)) {Y | IsUnit (1 - Y).det} := by sorry
