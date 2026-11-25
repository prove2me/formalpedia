-- Prove2me | Theorems.Thm_PI_IsoDerivBFintype_minor_expand
-- name    : PI.IsoDerivBFintype.minor_expand
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:47.646676+00:00
-- url     : https://prove2.me/theorems/3eb822ef-a298-4267-b888-c1b8a14a0067
-- title:
--   Iso Deriv BFintype: minor expand
-- statement:
--   The Iso Deriv BFintype construction uses the minor expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/IsoDerivB.lean#L25-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/IsoDerivB.lean#L25-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_IsoDerivB
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
open PI PI.IsoDerivBFintype
open PI.IsoDerivB
variable {T : Type} {N N' : ℕ} (s : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ)

theorem PI.IsoDerivBFintype.minor_expand (τ : T) {h : ℕ} (Jc : Fin h ↪o Fin N) :
    MvPolynomial.aeval (gD s y') (Matrix.det (Matrix.of fun i j : Fin h =>
      if hj : (j : ℕ) < N then (MvPolynomial.X (τ, Jc i, ⟨j, hj⟩) : MvPolynomial (FrV T N) ℂ)
      else 0))
    = ∑ I : Fin h ↪o Fin N', Matrix.det (Matrix.of fun i k : Fin h =>
        MvPolynomial.C (s τ) *
          (MvPolynomial.X ((τ, I i, Jc k) : Idx T N N') : MvPolynomial (Idx T N N') ℂ)) *
      MvPolynomial.C (Matrix.det (Matrix.of fun i j : Fin h => colsOf (y' τ) (I i) (j : ℕ))) := by sorry
