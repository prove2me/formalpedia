-- Prove2me | Theorems.Thm_PI_WAU_Cpt_nat_smul_mul_eq
-- name    : PI.WAU.Cpt.nat_smul_mul_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:44:26.794682+00:00
-- url     : https://prove2.me/theorems/b8ecee41-03db-4672-acba-b8e588cfc01f
-- title:
--   Cpt: nat smul mul eq
-- statement:
--   The Cpt construction uses the nat smul mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/NatSmulMulEq.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/NatSmulMulEq.lean#L99-L102

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_NatSmulMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)

theorem PI.WAU.Cpt.nat_smul_mul_eq (g d D m : ℕ) (a y : I.E ⊗[I.F] Af I.F) :
    ((g * d * D * m) • a) * y = (g * d) • (m • (a * (D • y))) := by sorry
