-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_zT_sat
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.rep_zT_sat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:14.091881+00:00
-- url     : https://prove2.me/theorems/71f04bcd-bd59-495e-904d-b72f1104ee7c
-- title:
--   Unimod Loc Std: rep z T sat
-- statement:
--   The Unimod Loc Std construction uses the rep z T sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepSingleSat.lean#L192-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepSingleSat.lean#L192-L206

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
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
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.rep_zT_sat (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) (x y : ℤ) (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (T : Finset m)
    (hT : ∀ j ∈ T, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) {z : m → ℂ} (hz : z ∈ Λ) :
    SatMem l Λ (zT T z) := by sorry
