-- Prove2me | Theorems.Thm_PI_GGConvScalarW_projQ_comp_pi
-- name    : PI.GGConvScalarW.projQ_comp_pi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:03.128977+00:00
-- url     : https://prove2.me/theorems/c1f0fccc-53fb-455c-ba55-bb09b425f5cd
-- title:
--   GGConv Scalar W: proj Q comp pi
-- statement:
--   The GGConv Scalar W construction uses the proj Q comp pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/AveragingOperatorIdempotent.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/AveragingOperatorIdempotent.lean#L35-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_AveragingOperatorIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem PI.GGConvScalarW.projQ_comp_pi (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) {u : GL (Fin k) F}
    (hu : IsUni k u) : projQ ψ₀ π ∘ₗ π u = (psiU ψ₀ u)⁻¹ • projQ ψ₀ π := by sorry
