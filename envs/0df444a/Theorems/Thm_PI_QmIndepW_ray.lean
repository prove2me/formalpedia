-- Prove2me | Theorems.Thm_PI_QmIndepW_ray
-- name    : PI.QmIndepW.ray
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:14.548114+00:00
-- url     : https://prove2.me/theorems/009fd934-d239-5ad7-b3ac-e46eb61de8f6
-- title:
--   Qm Indep W: ray
-- statement:
--   The Qm Indep W construction uses the ray property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuarticIndependence/IndepC.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuarticIndependence/IndepC.lean#L32-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmIndepW
open Complex

theorem PI.QmIndepW.ray (y00 y10 y20 y01 y11 y21 y02 y12 y22 : ℂ)
    (hyp : ∀ c : ℂ, c ≠ 0 → nine c⁻¹ (star c)⁻¹ y00 y10 y20 y01 y11 y21 y02 y12 y22 = 0)
    (ω ω' : ℂ) (hω : ω ≠ 0) (hs : star ω = ω') :
    y00 = 0 ∧ ω * y10 + ω' * y01 = 0 ∧ ω ^ 2 * y20 + ω * ω' * y11 + ω' ^ 2 * y02 = 0 ∧
      ω ^ 2 * ω' * y21 + ω * ω' ^ 2 * y12 = 0 ∧ ω ^ 2 * ω' ^ 2 * y22 = 0 := by sorry
