-- Prove2me | Theorems.Thm_PI_KLW_Ind_extL_ne
-- name    : PI.KLW.Ind.extL_ne
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:29.611978+00:00
-- url     : https://prove2.me/theorems/adaf07f3-d67f-44e7-8540-71a77dd7466b
-- title:
--   Ind: ext L ne
-- statement:
--   The Ind construction uses the ext L ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/LatticeFromNormOneInduction.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/LatticeFromNormOneInduction.lean#L81-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Ind
open PI.KLW

theorem PI.KLW.Ind.extL_ne {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι)
    (w : {i // i ≠ i0} → K) (j : {i // i ≠ i0}) : extL i0 w j.1 = w j := by sorry
