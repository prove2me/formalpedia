-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_relK
-- name    : PI.OddDualWeyl.Red.relK
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:49.187924+00:00
-- url     : https://prove2.me/theorems/d712923e-999e-4ce5-9631-96e44ee74219
-- title:
--   Red: rel K
-- statement:
--   The Red construction uses the rel K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L256-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L256-L264

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

theorem PI.OddDualWeyl.Red.relK (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0)
    {p p' : MvPolynomial (Fin k × Fin k) K} {M D : ℕ} (hrel : Rel K k M p p') (hp' : p'.IsHomogeneous D)
    (c c' : K) (hc : c' * g.det ^ D * (g.det)⁻¹ ^ M = c) :
    dualSub K k (c' • rowAct K gᵀ p') = (genM K k).det ^ M * (c • rowAct K g⁻¹ p) := by sorry
