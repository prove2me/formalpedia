-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_rhsBy_succ
-- name    : PI.UnitaryGroupMassFormula.PhGram.ExpandW.rhsBy_succ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:36.625435+00:00
-- url     : https://prove2.me/theorems/c90e3805-e736-50e3-947e-6102ce37359a
-- title:
--   Expand W: rhs By succ
-- statement:
--   The Expand W construction uses the rhs By succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/Expand.lean#L142-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/Expand.lean#L142-L152

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram PI.UnitaryGroupMassFormula.PhGram.ExpandW
open PI.FglGram PI.UnitaryGroupMassFormula.PhGram
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]} {σ : Type}

theorem PI.UnitaryGroupMassFormula.PhGram.ExpandW.rhsBy_succ {m : ℕ} (a : Fin (m + 1) → MvPowerSeries σ ℂ_[p]) :
    rhsBy l ex ph a = rhsBy l ex ph (fun j : Fin m => a (Fin.castSucc j)) +
      (phAt ph (a (Fin.last m)) + ∑ j : Fin m, be l ex ph (a (Fin.castSucc j)) (a (Fin.last m))) := by sorry
