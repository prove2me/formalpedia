-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_locJacTyp_of
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.locJacTyp_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:01.650459+00:00
-- url     : https://prove2.me/theorems/047168dd-322e-5ee6-8179-e3258085e127
-- title:
--   Loc Jac Typ: loc Jac Typ of
-- statement:
--   The Loc Jac Typ construction uses the loc Jac Typ of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/Development.lean#L66-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/Development.lean#L66-L88

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

theorem PI.UnitaryGroupMassFormula.LocJacTyp.locJacTyp_of (h0 : SdNorm (E := E) ψ v) (hZ : VolZZ σ v) (hU : VolU σ v)
    (hP : VolPP σ v) (hA : Arith (F := F) v) : PI.LocJacTyp.LocJacTyp σ ψ v := by sorry
