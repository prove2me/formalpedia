-- Prove2me | Theorems.Thm_PI_Dv_IdxW_lenS_ne_top
-- name    : PI.Dv.IdxW.lenS_ne_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:02.447313+00:00
-- url     : https://prove2.me/theorems/4e022d1c-7970-5063-ab29-fec9c9f0e490
-- title:
--   Idx W: len S ne top
-- statement:
--   The Idx W construction uses the len S ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L245-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L245-L253

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open NumberField IsDedekindDomain Module
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.IdxW.lenS_ne_top (w : HeightOneSpectrum (𝓞 K)) (X Y : Submodule (𝓞 K) V) (hX : X.FG)
    {c : 𝓞 K} (hc : c ≠ 0) (h : ∀ x ∈ X, c • x ∈ Y) : lenS w.asIdeal.primeCompl X Y ≠ ⊤ := by sorry
