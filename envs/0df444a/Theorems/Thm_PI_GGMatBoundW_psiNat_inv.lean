-- Prove2me | Theorems.Thm_PI_GGMatBoundW_psiNat_inv
-- name    : PI.GGMatBoundW.psiNat_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:31:17.762813+00:00
-- url     : https://prove2.me/theorems/0f7aca6d-6205-405c-929c-082ac78a5cc7
-- title:
--   GGMat Bound W: psi Nat inv
-- statement:
--   The GGMat Bound W construction uses the psi Nat inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/GammaMatrixInverse.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/GammaMatrixInverse.lean#L22-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic PI.GGConvScalarW

theorem PI.GGMatBoundW.psiNat_inv {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) (u : GL (Fin k) F) :
    psiNat ψ₀ u⁻¹ = conj (psiNat ψ₀ u) := by sorry
