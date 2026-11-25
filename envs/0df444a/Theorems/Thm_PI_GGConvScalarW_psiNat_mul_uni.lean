-- Prove2me | Theorems.Thm_PI_GGConvScalarW_psiNat_mul_uni
-- name    : PI.GGConvScalarW.psiNat_mul_uni
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:44.022128+00:00
-- url     : https://prove2.me/theorems/059e0f96-4b25-41bb-ba48-4e4a28c737eb
-- title:
--   GGConv Scalar W: psi Nat mul uni
-- statement:
--   The GGConv Scalar W construction uses the psi Nat mul uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/AveragingOperatorIdempotent.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/AveragingOperatorIdempotent.lean#L17-L23

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

theorem PI.GGConvScalarW.psiNat_mul_uni (ψ₀ : AddChar F ℂ) (z : GL (Fin k) F) {u : GL (Fin k) F} (hu : IsUni k u) :
    psiNat ψ₀ (z * u) = psiNat ψ₀ z * psiU ψ₀ u := by sorry
