-- Prove2me | Theorems.Thm_PI_Dv_IdxW_idx_via
-- name    : PI.Dv.IdxW.idx_via
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:07.188827+00:00
-- url     : https://prove2.me/theorems/7e75cbdf-9c8e-49dc-b51e-17e386207dd0
-- title:
--   Idx W: idx via
-- statement:
--   The Idx W construction uses the idx via property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L257-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean#L257-L310

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
omit [Module K V] [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.IdxW.idx_via (w : HeightOneSpectrum (𝓞 K)) (M N D : Submodule (𝓞 K) V) (hDM : D ≤ M)
    (hDN : D ≤ N) (hM : lenS w.asIdeal.primeCompl M D ≠ ⊤)
    (hN : lenS w.asIdeal.primeCompl N D ≠ ⊤) :
    idxAt w M N = ((lenS w.asIdeal.primeCompl M D).toNat : ℤ) -
      (lenS w.asIdeal.primeCompl N D).toNat := by sorry
