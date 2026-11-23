-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_finite_eval_eq_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.bwp_finite_eval_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:38.488712+00:00
-- url     : https://prove2.me/theorems/6616a56a-abe3-4db6-a68f-3bcc48c38619
-- title:
--   Multiplicative Heights: bwp finite eval eq zero
-- statement:
--   The Multiplicative Heights construction uses the bwp finite eval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L12-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L12-L12

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial

theorem ReciprocityTheory.MultiplicativeHeights.bwp_finite_eval_eq_zero {P : ℂ[X]} (hP : P ≠ 0) : {t : ℂ | P.eval t = 0}.Finite := by sorry
