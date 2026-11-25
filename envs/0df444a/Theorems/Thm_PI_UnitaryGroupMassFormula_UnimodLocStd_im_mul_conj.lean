-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_im_mul_conj
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.im_mul_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:30.942824+00:00
-- url     : https://prove2.me/theorems/f813adb9-5766-4a33-b7b2-ca23fd799ab4
-- title:
--   Unimod Loc Std: im mul conj
-- statement:
--   The Unimod Loc Std construction uses the im mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SelfDualStd.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SelfDualStd.lean#L50-L55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.im_mul_conj (L : PeriodPair) (p q r s : ℝ) :
    ((p • L.ω₁ + q • L.ω₂) * conj (r • L.ω₁ + s • L.ω₂)).im = (q * r - p * s) * detD L := by sorry
