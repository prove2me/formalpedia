-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_Sd_coe_herm_smul
-- name    : PI.OmFibreUniq.W.Sd.coe_herm_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:00.056275+00:00
-- url     : https://prove2.me/theorems/25267163-c6c8-4d04-81a2-5f9199ac6044
-- title:
--   Sd: coe herm smul
-- statement:
--   The Sd construction uses the coe herm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SmulMemHermR.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SmulMemHermR.lean#L33-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.VolStabSW PI.VolStabSW.SdUniqW PI.AdicCompletionValuation
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (a : ℕ)

theorem PI.OmFibreUniq.W.Sd.coe_herm_smul (c : R) (S : HermR R σ a) :
    ((c • S : HermR R σ a) : Matrix (Fin a) (Fin a) (R ⊗[F] E)) = c • (S : Matrix _ _ _) := by sorry
