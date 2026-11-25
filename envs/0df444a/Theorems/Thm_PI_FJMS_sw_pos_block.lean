-- Prove2me | Theorems.Thm_PI_FJMS_sw_pos_block
-- name    : PI.FJMS.sw_pos_block
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:30:42.134873+00:00
-- url     : https://prove2.me/theorems/3cefc12e-d944-42e6-ba73-8c24565cb6ae
-- title:
--   FJMS: sw pos block
-- statement:
--   The FJMS construction uses the sw pos block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L106-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L106-L111

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP
variable {σ κ : Type*} [Fintype κ]

theorem PI.FJMS.sw_pos_block {m : ℕ} (e : σ →₀ ℕ) (w : κ → σ) (pos : κ → Bool) (j : Fin m → κ) (hj : Function.Injective j)
    (hA : ∀ c, c ∉ Set.range j → e (w c) = 0) (hin : ∀ k, pos (j k) = true) :
    sw e w pos = ((∑ k, e (w (j k)) : ℕ) : ℤ) := by sorry
