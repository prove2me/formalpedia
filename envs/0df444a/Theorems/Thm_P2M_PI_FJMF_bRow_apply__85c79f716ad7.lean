-- Prove2me | Theorems.Thm_P2M_PI_FJMF_bRow_apply__85c79f716ad7
-- name    : P2M_PI_FJMF_bRow_apply__85c79f716ad7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:32.1338+00:00
-- url     : https://prove2.me/theorems/afc9dfc2-9b05-4ff6-9cb0-b97c4e3156be
-- title:
--   P2 M PI FJMF b Row apply  85c79f716ad7: P2 M PI FJMF b Row apply  85c79f716ad7
-- statement:
--   The P2 M PI FJMF b Row apply  85c79f716ad7 construction uses the P2 M PI FJMF b Row apply  85c79f716ad7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/BlockDegreeAntitone.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/BlockDegreeAntitone.lean#L19-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PI PI.FJMF
variable {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ)

theorem P2M_PI_FJMF_bRow_apply__85c79f716ad7 (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by sorry

alias «PI».«FJMF».«bRow_apply'» := P2M_PI_FJMF_bRow_apply__85c79f716ad7
