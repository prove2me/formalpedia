-- Prove2me | Theorems.Thm_PI_Dv_IdxW_len_c
-- name    : PI.Dv.IdxW.len_c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:57.88395+00:00
-- url     : https://prove2.me/theorems/cb2583f3-ef58-5064-a8d5-d8a868205f9d
-- title:
--   Idx W: len c
-- statement:
--   The Idx W construction uses the len c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L225-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L225-L243

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

theorem PI.Dv.IdxW.len_c (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) (hM : M.FG) {c : 𝓞 K}
    (hc : c ≠ 0) :
    ∃ k : ℕ, Formalism.BasicNotions.vAdd w (algebraMap (𝓞 K) K c) = k ∧
      lenS w.asIdeal.primeCompl M (Ideal.span {c} • M) = ((k * Formalism.HN.rkK M : ℕ) : ℕ∞) := by sorry
