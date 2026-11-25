-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_key_mat
-- name    : PI.OddDualWeyl.Red.key_mat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:32.815802+00:00
-- url     : https://prove2.me/theorems/a8f1ca41-ba70-53b2-b096-0f0999224413
-- title:
--   Red: key mat
-- statement:
--   The Red construction uses the key mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L219-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L219-L229

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
variable {K : Type*} [Field K] {k : ℕ}

theorem PI.OddDualWeyl.Red.key_mat (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0) :
    cM gᵀ * dualM K k = (C g.det : MvPolynomial (Fin k × Fin k) K) • (dualM K k).map (sbs (cM g⁻¹ * genM K k)) := by sorry
