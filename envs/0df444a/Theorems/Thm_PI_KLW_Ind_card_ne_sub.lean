-- Prove2me | Theorems.Thm_PI_KLW_Ind_card_ne_sub
-- name    : PI.KLW.Ind.card_ne_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:33:23.569671+00:00
-- url     : https://prove2.me/theorems/130783eb-8a2d-528f-8026-aa9d23bd632e
-- title:
--   Ind: card ne sub
-- statement:
--   The Ind construction uses the card ne sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/LatticeFromNormOneInduction.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/LatticeFromNormOneInduction.lean#L178-L181

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

theorem PI.KLW.Ind.card_ne_sub {ι : Type} [Fintype ι] [DecidableEq ι] (i0 : ι) (k : ℕ)
    (hk : Fintype.card ι = k + 1) : Fintype.card {i // i ≠ i0} = k := by sorry
