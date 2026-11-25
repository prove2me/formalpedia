-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_SD_p_pt
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.SD.p_pt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:10.98783+00:00
-- url     : https://prove2.me/theorems/456515ed-acb1-49aa-b653-c2963ba378b9
-- title:
--   SD: p pt
-- statement:
--   The SD construction uses the p pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitShear.lean#L120-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitShear.lean#L120-L120

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitShear
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_locallyCompact_Fv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_secondCountable_Fv
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}
open PI.UnitaryGroupMassFormula.LocJacTyp.SD
variable (D : SD σ v)

theorem PI.UnitaryGroupMassFormula.LocJacTyp.SD.p_pt (s t : Fv F v) : D.p 0 (D.pt s t) = s ∧ D.p 1 (D.pt s t) = t := by sorry
