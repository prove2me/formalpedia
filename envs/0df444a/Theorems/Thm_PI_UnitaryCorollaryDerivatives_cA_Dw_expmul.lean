-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dw_expmul
-- name    : PI.UnitaryCorollaryDerivatives.cA_Dw_expmul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:00.195966+00:00
-- url     : https://prove2.me/theorems/2741b882-4beb-5faa-bf3c-78d1c8568608
-- title:
--   Unitary Corollary Derivatives: c A Dw expmul
-- statement:
--   The Unitary Corollary Derivatives construction uses the c A Dw expmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L97-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CADwlSmooth.lean#L97-L128

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.UnitaryCorollaryDerivatives.cA_Dw_expmul (lam : Bool × B.Mat k r → ℂ) (h : B.Mat k r → ℂ) :
    ∀ (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      (∀ x ∈ w, ∀ g (t : ℝ), h (crv x g t) = Complex.exp ((t : ℂ) * lam x) * h g) →
      Dw w (fun g => h g • F g) = fun g => h g • Dwl lam w F g := by sorry
