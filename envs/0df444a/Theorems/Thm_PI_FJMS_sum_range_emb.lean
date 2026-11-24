-- Prove2me | Theorems.Thm_PI_FJMS_sum_range_emb
-- name    : PI.FJMS.sum_range_emb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:49.038801+00:00
-- url     : https://prove2.me/theorems/6387c83f-b6d2-4523-8103-2fac34207491
-- title:
--   FJMS: sum range emb
-- statement:
--   The FJMS construction uses the sum range emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L80-L85

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

theorem PI.FJMS.sum_range_emb {M : Type*} [AddCommMonoid M] {m : ℕ} (j : Fin m → κ) (hj : Function.Injective j)
    (f : κ → M) (hf : ∀ c, c ∉ Set.range j → f c = 0) : ∑ c, f c = ∑ k, f (j k) := by sorry
