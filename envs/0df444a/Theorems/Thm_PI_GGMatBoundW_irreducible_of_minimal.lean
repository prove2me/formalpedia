-- Prove2me | Theorems.Thm_PI_GGMatBoundW_irreducible_of_minimal
-- name    : PI.GGMatBoundW.irreducible_of_minimal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:58:00.714793+00:00
-- url     : https://prove2.me/theorems/1b409f73-a165-4c91-88c3-149d7944fb2c
-- title:
--   GGMat Bound W: irreducible of minimal
-- statement:
--   The GGMat Bound W construction uses the irreducible of minimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/IrreducibleOfMinimal.lean#L19-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/IrreducibleOfMinimal.lean#L19-L54

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_RepresentationDimensionPos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_IrreducibleOfMinimal
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
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem PI.GGMatBoundW.irreducible_of_minimal (π : Representation ℂ G V) (W : Subrepresentation π) (hW : W ≠ ⊥)
    (hmin : ∀ W' : Subrepresentation π, W' ≠ ⊥ → W' ≤ W →
      Module.finrank ℂ W.toSubmodule ≤ Module.finrank ℂ W'.toSubmodule) :
    W.toRepresentation.IsIrreducible := by sorry
