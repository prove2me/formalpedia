-- Prove2me | Theorems.Thm_P2M_PI_FJMS_bRow_apply__fa8f98d64b0d
-- name    : P2M_PI_FJMS_bRow_apply__fa8f98d64b0d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:50.602853+00:00
-- url     : https://prove2.me/theorems/9818738e-97b0-46a8-ad7f-957cf8736637
-- title:
--   P2 M PI FJMS b Row apply  fa8f98d64b0d: P2 M PI FJMS b Row apply  fa8f98d64b0d
-- statement:
--   The P2 M PI FJMS b Row apply  fa8f98d64b0d construction uses the P2 M PI FJMS b Row apply  fa8f98d64b0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L120-L122

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

theorem P2M_PI_FJMS_bRow_apply__fa8f98d64b0d {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by sorry

alias «PI».«FJMS».«bRow_apply'» := P2M_PI_FJMS_bRow_apply__fa8f98d64b0d
