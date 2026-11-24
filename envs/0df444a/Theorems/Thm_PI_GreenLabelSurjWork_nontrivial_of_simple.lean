-- Prove2me | Theorems.Thm_PI_GreenLabelSurjWork_nontrivial_of_simple
-- name    : PI.GreenLabelSurjWork.nontrivial_of_simple
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:12.952762+00:00
-- url     : https://prove2.me/theorems/996cbabc-2aa6-4663-9d1f-71f1a8dc142f
-- title:
--   Green Label Surj Work: nontrivial of simple
-- statement:
--   The Green Label Surj Work construction uses the nontrivial of simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Simple.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Simple.lean#L20-L27

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.GreenLabelSurjWork
variable {G : Type} [Group G] [Fintype G]

theorem PI.GreenLabelSurjWork.nontrivial_of_simple (V : FDRep ℂ G) (h : Simple V) : Nontrivial V := by sorry
