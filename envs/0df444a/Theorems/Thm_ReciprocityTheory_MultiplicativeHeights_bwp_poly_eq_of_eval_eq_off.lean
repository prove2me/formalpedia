-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_poly_eq_of_eval_eq_off
-- name    : ReciprocityTheory.MultiplicativeHeights.bwp_poly_eq_of_eval_eq_off
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:39.955278+00:00
-- url     : https://prove2.me/theorems/e2461c82-18fe-46be-b131-c535bd7e4045
-- title:
--   Multiplicative Heights: bwp poly eq of eval eq off
-- statement:
--   The Multiplicative Heights construction uses the bwp poly eq of eval eq off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L7-L10

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

theorem ReciprocityTheory.MultiplicativeHeights.bwp_poly_eq_of_eval_eq_off (P Q : ℂ[X]) (E : Set ℂ) (hE : E.Finite)
    (h : ∀ t ∉ E, P.eval t = Q.eval t) : P = Q := by sorry
