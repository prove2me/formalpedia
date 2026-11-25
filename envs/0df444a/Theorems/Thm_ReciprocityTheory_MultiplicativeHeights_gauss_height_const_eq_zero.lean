-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_height_const_eq_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_height_const_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:06.611825+00:00
-- url     : https://prove2.me/theorems/6dc4134d-69a7-55d7-b338-14be81eb57c3
-- title:
--   Multiplicative Heights: gauss height const eq zero
-- statement:
--   The Multiplicative Heights construction uses the gauss height const eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LagrangeIdealLiftsFact.lean#L77-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LagrangeIdealLiftsFact.lean#L77-L131

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory NumberField

theorem ReciprocityTheory.MultiplicativeHeights.gauss_height_const_eq_zero {K : Type*} [Field K] [NumberField K] (B n : ℕ) (hn : 0 < n) (c : K)
    (hc : c ≠ 0) : h0 (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) = 0 := by sorry
