-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_coord_mem
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.coord_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:35:22.662499+00:00
-- url     : https://prove2.me/theorems/aeb1291c-b9df-43ec-8ad8-2c1bf4868d66
-- title:
--   Unimod Loc Std: coord mem
-- statement:
--   The Unimod Loc Std construction uses the coord mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SatStdOfAll.lean#L44-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SatStdOfAll.lean#L44-L77

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SatStdOfAll
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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.coord_mem (hn : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c) (x y : ℤ) (n : ℕ) (w : ℂ)
    (h1 : ∃ k : ℤ, (n : ℝ) * (w * conj (lam * ((x * a : ℂ) + y * cmTheta b d))).im
      / area (cmL a b d ha hd lam hlam) = k)
    (h2 : ∃ k : ℤ, (n : ℝ) * (w * conj (cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)))).im
      / area (cmL a b d ha hd lam hlam) = k) :
    ((n * (a * x ^ 2 + b * x * y + c * y ^ 2) : ℤ) : ℂ) * w ∈ (cmL a b d ha hd lam hlam).lattice := by sorry
