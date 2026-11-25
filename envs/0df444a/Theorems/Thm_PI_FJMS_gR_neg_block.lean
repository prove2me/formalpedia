-- Prove2me | Theorems.Thm_PI_FJMS_gR_neg_block
-- name    : PI.FJMS.gR_neg_block
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:59.650592+00:00
-- url     : https://prove2.me/theorems/b1cfedad-6e14-4241-8011-fbcbc22bbed4
-- title:
--   FJMS: g R neg block
-- statement:
--   The FJMS construction uses the g R neg block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L98-L104

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

theorem PI.FJMS.gR_neg_block {m : ℕ} (u v : κ → σ) (pos : κ → Bool) (j : Fin m → κ) (hj : Function.Injective j)
    (P : MvPolynomial σ ℂ) (hA : ∀ c, c ∉ Set.range j → NoVar P (u c))
    (hB : ∀ c, c ∉ Set.range j → NoVar P (v c)) (hin : ∀ k, pos (j k) = false) :
    gR u v pos P = -∑ k, X (v (j k)) * pderiv (u (j k)) P := by sorry
