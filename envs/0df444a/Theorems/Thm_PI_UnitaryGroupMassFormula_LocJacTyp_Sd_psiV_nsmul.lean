-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_nsmul
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.psiV_nsmul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:59:51.237661+00:00
-- url     : https://prove2.me/theorems/08faf75a-0149-4758-be02-910f5b8dcf4a
-- title:
--   Sd: psi V nsmul
-- statement:
--   The Sd construction uses the psi V nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ContinuousPsiVOf.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ContinuousPsiVOf.lean#L59-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousPsiVOf
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable (ψ : AddChar (AF F) ℂ)

theorem PI.UnitaryGroupMassFormula.LocJacTyp.Sd.psiV_nsmul (n : ℕ) (r : Fv F v) : psiV F ψ v (n • r) = psiV F ψ v r ^ n := by sorry
