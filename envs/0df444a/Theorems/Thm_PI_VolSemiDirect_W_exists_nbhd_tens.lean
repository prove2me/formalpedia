-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_exists_nbhd_tens
-- name    : PI.VolSemiDirect.W.exists_nbhd_tens
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:36:47.857365+00:00
-- url     : https://prove2.me/theorems/d4557081-c26b-426e-bd56-67eea7c61752
-- title:
--   W: exists nbhd tens
-- statement:
--   The W construction uses the exists nbhd tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/EqZeroOfMemNbhdA.lean#L69-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/EqZeroOfMemNbhdA.lean#L69-L89

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [Module.Finite F E]

theorem PI.VolSemiDirect.W.exists_nbhd_tens : ∃ U : Set (AF F ⊗[F] E), IsOpen U ∧ (0 : AF F ⊗[F] E) ∈ U ∧
    ∀ e : E, inclR (F := F) (AF F) e ∈ U → e = 0 := by sorry
