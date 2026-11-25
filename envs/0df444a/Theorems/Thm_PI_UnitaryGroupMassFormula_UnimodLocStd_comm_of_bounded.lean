-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_comm_of_bounded
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.comm_of_bounded
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:35:06.351578+00:00
-- url     : https://prove2.me/theorems/022f82a3-9119-58a7-b4c6-942163cfb4ec
-- title:
--   Unimod Loc Std: comm of bounded
-- statement:
--   The Unimod Loc Std construction uses the comm of bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/CommOfBounded.lean#L190-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/CommOfBounded.lean#L190-L212

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.comm_of_bounded (σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) {N N' : ℕ} (hN : N ≠ 0) (hN' : N' ≠ 0)
    (h1 : ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m, N • σ s ∈ stdLat (cmL a b d ha hd lam hlam) m)
    (h2 : ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m, N' • σ.symm s ∈ stdLat (cmL a b d ha hd lam hlam) m) :
    relIdx (stdLat (cmL a b d ha hd lam hlam) m)
        (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m))
        (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 := by sorry
