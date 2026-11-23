-- Prove2me | Theorems.Thm_PI_GreenLabelSurjWork_simple_of_irr
-- name    : PI.GreenLabelSurjWork.simple_of_irr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:10.991049+00:00
-- url     : https://prove2.me/theorems/4bbaff83-f301-4fed-adac-c5e33a8fc0c4
-- title:
--   Green Label Surj Work: simple of irr
-- statement:
--   The Green Label Surj Work construction uses the simple of irr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Simple.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Simple.lean#L13-L18

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

theorem PI.GreenLabelSurjWork.simple_of_irr {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [σ.IsIrreducible] : Simple (FDRep.of σ) := by sorry
