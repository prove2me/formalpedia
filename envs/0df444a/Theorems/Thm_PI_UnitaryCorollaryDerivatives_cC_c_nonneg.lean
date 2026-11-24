-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cC_c_nonneg
-- name    : PI.UnitaryCorollaryDerivatives.cC_c_nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:53:06.39402+00:00
-- url     : https://prove2.me/theorems/256fe25b-35cf-41af-b34b-7376f2ed6a98
-- title:
--   Unitary Corollary Derivatives: c C c nonneg
-- statement:
--   The Unitary Corollary Derivatives construction uses the c C c nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CCCNonneg.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CCCNonneg.lean#L19-L23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.UnitaryCorollaryDerivatives.cC_c_nonneg {r : ℕ} {A : ℝ} {m : ℕ} {f : B.Mat k r → E} {c : ℝ} (hf : B.CCle A m f c) : 0 ≤ c := by sorry
