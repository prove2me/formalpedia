-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TM_sum_emb
-- name    : PI.PolynomialProperness.TM.sum_emb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:30:51.158822+00:00
-- url     : https://prove2.me/theorems/9268a497-caeb-44fe-849e-be77e9904680
-- title:
--   TM: sum emb
-- statement:
--   The TM construction uses the sum emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L10-L20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.TM

theorem PI.PolynomialProperness.TM.sum_emb {N n : ℕ} (e : Fin n ↪ Fin N) (f : Fin N → ℂ) (hf : ∀ i, (∀ t, e t ≠ i) → f i = 0) :
    ∑ i, f i = ∑ t, f (e t) := by sorry
