-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_st_nsmul
-- name    : PI.GalTorsConj.W.st_nsmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:08.00511+00:00
-- url     : https://prove2.me/theorems/bc212596-e522-4c43-9acb-020c58f80db6
-- title:
--   W: st nsmul
-- statement:
--   The W construction uses the st nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/StAddRight.lean#L231-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/StAddRight.lean#L231-L241

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

theorem PI.GalTorsConj.W.st_nsmul (hA : AddLaw) (hD : DblLaw) (hg2 : L.g₂ ∈ M) (hg2' : L'.g₂ = ρ ⟨_, hg2⟩)
    {t t' : ℂ} (h : St L L' M ρ t t') (n : ℕ) :
    St L L' M ρ ((n : ℂ) * t) ((n : ℂ) * t') := by sorry
