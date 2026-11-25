-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_SD_p_sig
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.SD.p_sig
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:16.095737+00:00
-- url     : https://prove2.me/theorems/552a79d0-ea65-444c-a465-65d56ef4347f
-- title:
--   SD: p sig
-- statement:
--   The SD construction uses the p sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitSplit.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitSplit.lean#L53-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
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
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
open PI.UnitaryGroupMassFormula.LocJacTyp.SD
variable {σ v} (D : SD σ v)

theorem PI.UnitaryGroupMassFormula.LocJacTyp.SD.p_sig (z : Fv F v ⊗[F] E) :
    D.p 0 (sigR (Fv F v) σ z) = D.p 1 z ∧ D.p 1 (sigR (Fv F v) σ z) = D.p 0 z := by sorry
