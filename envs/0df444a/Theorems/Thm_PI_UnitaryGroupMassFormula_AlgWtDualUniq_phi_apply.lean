-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AlgWtDualUniq_phi_apply
-- name    : PI.UnitaryGroupMassFormula.AlgWtDualUniq.phi_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:09.161058+00:00
-- url     : https://prove2.me/theorems/5037c4da-f00e-4de4-9520-ac39c93d89ef
-- title:
--   Alg Wt Dual Uniq: phi apply
-- statement:
--   The Alg Wt Dual Uniq construction uses the phi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightDualUniqueness/SelfInjective.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightDualUniqueness/SelfInjective.lean#L76-L78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightDualUniqueness_SelfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AlgWtDualUniq
open Module
variable {G : Type*} [Group G] {Va Vb : Type*} [AddCommGroup Va] [Module ℂ Va] [AddCommGroup Vb] [Module ℂ Vb]
  (ρa : Representation ℂ G Va) (ρb : Representation ℂ G Vb)
variable {ρa ρb}

theorem PI.UnitaryGroupMassFormula.AlgWtDualUniq.phi_apply [FiniteDimensional ℂ Va] [FiniteDimensional ℂ Vb] [ρa.IsIrreducible] [ρb.IsIrreducible]
    (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) (y : Vb) (x : Va) :
    phi B hB h0 y x = B x y := by sorry
