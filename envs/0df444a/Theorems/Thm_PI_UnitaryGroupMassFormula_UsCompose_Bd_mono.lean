-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_Bd_mono
-- name    : PI.UnitaryGroupMassFormula.UsCompose.Bd.mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:33:03.949856+00:00
-- url     : https://prove2.me/theorems/6902b542-cb5f-446a-b664-f17aa6a73ade
-- title:
--   Bd: mono
-- statement:
--   The Bd construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L29-L31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PI.UnitaryGroupMassFormula.UsCompose.Bd.mono {k j ρ κ ℓ κ' ℓ' : ℕ} {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) (hκ : κ ≤ κ')
    (hℓ : ℓ ≤ ℓ') : Bd k j ρ κ' ℓ' L := by sorry
