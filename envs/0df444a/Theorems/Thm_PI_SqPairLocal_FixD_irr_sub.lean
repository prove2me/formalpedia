-- Prove2me | Theorems.Thm_PI_SqPairLocal_FixD_irr_sub
-- name    : PI.SqPairLocal.FixD.irr_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:40.502817+00:00
-- url     : https://prove2.me/theorems/3a1cb7ef-780e-4f6a-a88a-469d492ac113
-- title:
--   Fix D: irr sub
-- statement:
--   The Fix D construction uses the irr sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean#L27-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open PI PI.SqPairLocal PI.SqPairLocal.FixD
variable {R : Type} [CommRing R] [IsDomain R] (σ : R ≃+* R)

theorem PI.SqPairLocal.FixD.irr_sub {ϖ : R} (hϖ : Irreducible ϖ) (h : ϖ ∈ fixSub σ) :
    Irreducible (⟨ϖ, h⟩ : fixSub σ) := by sorry
