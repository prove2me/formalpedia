-- Prove2me | Theorems.Thm_PI_GGMatBoundW_eig_place
-- name    : PI.GGMatBoundW.eig_place
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:31:21.682346+00:00
-- url     : https://prove2.me/theorems/25f95638-3e38-4f32-9ee0-16cf2b3ae503
-- title:
--   GGMat Bound W: eig place
-- statement:
--   The GGMat Bound W construction uses the eig place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/IrreducibleOfMinimal.lean#L107-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/IrreducibleOfMinimal.lean#L107-L177

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
variable {F : Type} [Field F] [Fintype F] {k : ℕ}

theorem PI.GGMatBoundW.eig_place (hC : ConvScalar) (hR : GenericRatio) (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1)
    (hq : 3 ≤ Fintype.card F) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V) (c : ℂ) (w : V) (hw : w ≠ 0)
    (hc : repGam ψ₀ π w = c • w) :
    ∃ r : ℝ, c = r ∧ 0 ≤ r ∧
      r ≤ (gam ψ₀ (1 : GL (Fin k) F)).re * (1 + 3 / (Fintype.card F : ℝ)) := by sorry
