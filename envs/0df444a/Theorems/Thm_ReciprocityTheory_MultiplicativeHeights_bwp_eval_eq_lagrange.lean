-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_eval_eq_lagrange
-- name    : ReciprocityTheory.MultiplicativeHeights.bwp_eval_eq_lagrange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:31.660868+00:00
-- url     : https://prove2.me/theorems/d3095f65-a0c8-4805-bab3-76dcc80bc75b
-- title:
--   Multiplicative Heights: bwp eval eq lagrange
-- statement:
--   The Multiplicative Heights construction uses the bwp eval eq lagrange property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L19-L30

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

theorem ReciprocityTheory.MultiplicativeHeights.bwp_eval_eq_lagrange (S : Finset ℂ) (Q : ℂ[X]) (k : ℕ) (hS : S.card = k + 1)
    (hQ : Q.natDegree ≤ k) (x : ℂ) :
    Q.eval x = ∑ c ∈ S, (Lagrange.basis S id c).eval x * Q.eval c := by sorry
