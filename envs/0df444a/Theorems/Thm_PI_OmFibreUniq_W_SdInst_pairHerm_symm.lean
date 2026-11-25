-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_SdInst_pairHerm_symm
-- name    : PI.OmFibreUniq.W.SdInst.pairHerm_symm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:15:15.7254+00:00
-- url     : https://prove2.me/theorems/07d1ef97-a1d9-52a1-8828-7c020cf80e82
-- title:
--   Sd Inst: pair Herm symm
-- statement:
--   The Sd Inst construction uses the pair Herm symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExInst.lean#L85-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExInst.lean#L85-L93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExInst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdInst
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd PI.OmFibreUniq.W.SdAbs
open PI.VolStabSW PI.VolStabSW.SdUniqW PI.VolStabSW.SdDualW PI.AdicCompletionValuation
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem PI.OmFibreUniq.W.SdInst.pairHerm_symm (σ : E →ₐ[F] E) (a : ℕ) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a S T = pairHerm (Fv F v) σ a T S := by sorry
