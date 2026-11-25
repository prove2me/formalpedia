-- Prove2me | Theorems.Thm_PI_Dv_IdxW_fact
-- name    : PI.Dv.IdxW.fact
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:11.296289+00:00
-- url     : https://prove2.me/theorems/db739336-fd98-46e6-872c-12c9051680e6
-- title:
--   Idx W: fact
-- statement:
--   The Idx W construction uses the fact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L142-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L142-L178

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

theorem PI.Dv.IdxW.fact (w : HeightOneSpectrum (𝓞 K)) {c : 𝓞 K} (hc : c ≠ 0) :
    ∃ k : ℕ, Formalism.BasicNotions.vAdd w (algebraMap (𝓞 K) K c) = k ∧ c ∈ w.asIdeal ^ k ∧
      ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∀ y ∈ w.asIdeal ^ k, s * y ∈ Ideal.span {c} := by sorry
