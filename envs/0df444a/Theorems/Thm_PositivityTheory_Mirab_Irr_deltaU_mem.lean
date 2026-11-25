-- Prove2me | Theorems.Thm_PositivityTheory_Mirab_Irr_deltaU_mem
-- name    : PositivityTheory.Mirab.Irr.deltaU_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T18:21:59.821277+00:00
-- url     : https://prove2.me/theorems/d68c28cd-e34a-56cb-929e-3c5061df961e
-- title:
--   Irr: delta U mem
-- statement:
--   The Irr construction uses the delta U mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndIrr.lean#L41-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndIrr.lean#L41-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open PositivityTheory PositivityTheory.Mirab PositivityTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)

theorem PositivityTheory.Mirab.Irr.deltaU_mem (ψ₀ : AddChar k ℂ) : deltaU n ψ₀ ∈ MirabInducedSpace n ψ₀ := by sorry
