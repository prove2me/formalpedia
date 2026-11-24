-- Prove2me | Theorems.Thm_P2M_PI_FJMS_bCol_apply__63c2c4b09970
-- name    : P2M_PI_FJMS_bCol_apply__63c2c4b09970
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:35.897293+00:00
-- url     : https://prove2.me/theorems/5db33972-4b27-426f-b532-13fad9180b4f
-- title:
--   P2 M PI FJMS b Col apply  63c2c4b09970: P2 M PI FJMS b Col apply  63c2c4b09970
-- statement:
--   The P2 M PI FJMS b Col apply  63c2c4b09970 construction uses the P2 M PI FJMS b Col apply  63c2c4b09970 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L124-L126

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

theorem P2M_PI_FJMS_bCol_apply__63c2c4b09970 {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (P : MvPolynomial σ ℂ) :
    bCol ι c d P = ∑ i : Fin m, X (ι (i, c)) * pderiv (ι (i, d)) P := by sorry

alias «PI».«FJMS».«bCol_apply'» := P2M_PI_FJMS_bCol_apply__63c2c4b09970
