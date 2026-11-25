-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_norm_f
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.rep_norm_f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:46.818363+00:00
-- url     : https://prove2.me/theorems/fc24f884-3456-4a9a-b232-38753a9e1505
-- title:
--   Unimod Loc Std: rep norm f
-- statement:
--   The Unimod Loc Std construction uses the rep norm f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepArith.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepArith.lean#L70-L77

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
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
variable (m : Type) [Fintype m] [DecidableEq m]

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.rep_norm_f (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) (x y : ℤ) (i₀ : m) :
    stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀) =
      repKappa a b d ha hd lam hlam * ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℂ) := by sorry
