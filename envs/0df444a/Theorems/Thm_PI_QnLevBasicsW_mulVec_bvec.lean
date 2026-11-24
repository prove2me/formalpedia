-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_mulVec_bvec
-- name    : PI.QnLevBasicsW.mulVec_bvec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:50.713958+00:00
-- url     : https://prove2.me/theorems/358d8bca-68bf-4168-828e-e24471c5ef89
-- title:
--   Qn Lev Basics W: mul Vec bvec
-- statement:
--   The Qn Lev Basics W construction uses the mul Vec bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L64-L65

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}

theorem PI.QnLevBasicsW.mulVec_bvec {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (q p : Fin m) : (M *ᵥ bvec q) p = M p q := by sorry
