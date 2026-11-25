-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_add__9a67760e36c5
-- name    : P2M_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_add__9a67760e36c5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:35.656324+00:00
-- url     : https://prove2.me/theorems/bc4c57f9-9e0d-56eb-a931-b3c920ace1a6
-- title:
--   P2 M PI Unitary Group Mass Formula Loc Jac Typ Sd psi V add  9a67760e36c5: P2 M PI Unitary Group Mass Formula Loc Jac Typ Sd psi V add  9a67760e36c5
-- statement:
--   The P2 M PI Unitary Group Mass Formula Loc Jac Typ Sd psi V add  9a67760e36c5 construction uses the P2 M PI Unitary Group Mass Formula Loc Jac Typ Sd psi V add  9a67760e36c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ContinuousPsiVOf.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ContinuousPsiVOf.lean#L46-L47

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

theorem P2M_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_add__9a67760e36c5 (r s : Fv F v) : psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by sorry

alias «PI».«UnitaryGroupMassFormula».«LocJacTyp».«Sd».«psiV_add'» := P2M_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_add__9a67760e36c5
