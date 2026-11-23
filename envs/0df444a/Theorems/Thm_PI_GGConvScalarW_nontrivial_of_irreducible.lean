-- Prove2me | Theorems.Thm_PI_GGConvScalarW_nontrivial_of_irreducible
-- name    : PI.GGConvScalarW.nontrivial_of_irreducible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:50.462349+00:00
-- url     : https://prove2.me/theorems/b75ed356-2445-4ceb-a4d4-e3f0788bf3ca
-- title:
--   GGConv Scalar W: nontrivial of irreducible
-- statement:
--   The GGConv Scalar W construction uses the nontrivial of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/RepresentationDimensionPos.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/RepresentationDimensionPos.lean#L12-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_RepresentationDimensionPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic

theorem PI.GGConvScalarW.nontrivial_of_irreducible {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : π.IsIrreducible) : Nontrivial V := by sorry
