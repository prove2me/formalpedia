-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cB_wP
-- name    : PI.UnitaryCorollaryDerivatives.cB_wP
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:49:21.130495+00:00
-- url     : https://prove2.me/theorems/bc2072eb-f5ec-418c-9e98-c286ebc9b21c
-- title:
--   Unitary Corollary Derivatives: c B w P
-- statement:
--   The Unitary Corollary Derivatives construction uses the c B w P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CBLamnorm.lean#L82-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CBLamnorm.lean#L82-L88

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm
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

theorem PI.UnitaryCorollaryDerivatives.cB_wP {k j ρ : ℕ} {u v : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) (hv : unitP k j ρ v) :
    ∀ x ∈ wL u ++ wR v, inLieP k j ρ x.2 ∧ ∀ a b, ‖x.2 a b‖ ≤ 1 := by sorry
