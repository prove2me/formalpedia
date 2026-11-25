-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_dualSub_rowAct
-- name    : PI.OddDualWeyl.Red.dualSub_rowAct
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:58.192857+00:00
-- url     : https://prove2.me/theorems/f0552510-3d78-421c-9056-5f043a4af862
-- title:
--   Red: dual Sub row Act
-- statement:
--   The Red construction uses the dual Sub row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L231-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L231-L254

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

theorem PI.OddDualWeyl.Red.dualSub_rowAct (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0)
    {p p' : MvPolynomial (Fin k × Fin k) K} {M D : ℕ} (hrel : Rel K k M p p') (hp' : p'.IsHomogeneous D) :
    dualSub K k (rowAct K gᵀ p') =
      C g.det ^ D * ((C (g.det)⁻¹ * (genM K k).det) ^ M * rowAct K g⁻¹ p) := by sorry
