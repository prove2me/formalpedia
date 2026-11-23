-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_st_inj
-- name    : PI.GalTorsConj.W.st_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:15.351798+00:00
-- url     : https://prove2.me/theorems/692e5cab-2e7e-4b60-b896-b7f5cd09b9d6
-- title:
--   W: st inj
-- statement:
--   The W construction uses the st inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/StAddRight.lean#L118-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/StAddRight.lean#L118-L128

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_StAddRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
variable {L L' : PeriodPair} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}

theorem PI.GalTorsConj.W.st_inj {t u s : ℂ} (h1 : St L L' M ρ t s) (h2 : St L L' M ρ u s) :
    t - u ∈ L.lattice := by sorry
