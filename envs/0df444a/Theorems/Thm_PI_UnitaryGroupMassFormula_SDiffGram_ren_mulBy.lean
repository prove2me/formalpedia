-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_ren_mulBy
-- name    : PI.UnitaryGroupMassFormula.SDiffGram.ren_mulBy
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:36:09.005319+00:00
-- url     : https://prove2.me/theorems/e7829921-cdfa-5cc5-92a3-3f47c0d103c4
-- title:
--   SDiff Gram: ren mul By
-- statement:
--   The SDiff Gram construction uses the ren mul By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramDifferenceRenaming/RenGramRhs.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramDifferenceRenaming/RenGramRhs.lean#L52-L59

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_RenGramRhs
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_expMv_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_int_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_simeq_iff_good
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_cc_lin
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_C
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_PhOn
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_X
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_be
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_lin
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_psubst
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_simeq_ren

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SDiffGram
open PI.FglGram MvPowerSeries
open PI.UnitaryGroupMassFormula.PhDualGram (ren ren_apply ren_psubst ren_X ren_C simeq_ren cc_lin ren_lin ren_be ren_PhOn)
open PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram (Good simeq_iff_good good_add good_sub expMv_zero int_one)
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}

theorem PI.UnitaryGroupMassFormula.SDiffGram.ren_mulBy (hl0 : PowerSeries.constantCoeff l = 0) {σ τ : Type} [Finite σ] (r : σ → τ)
    (c : ℂ_[p]) {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) :
    ren (p := p) r (mulBy l ex c x) = mulBy l ex c (ren r x) := by sorry
