-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_subset_eq_empty_of_internal_expansion_and_external_degree_lt
-- name    : QEC.Coding.SmallSetExpansion.subset_eq_empty_of_internal_expansion_and_external_degree_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:48:07.238578+00:00
-- url     : https://prove2.me/theorems/f669065d-accc-4fd5-b45c-4cef96ada73e
-- title:
--   Small Set Expansion: subset eq empty of internal expansion and external degree lt
-- statement:
--   The counting core of PK22's labelled-edge lemma.  Let `A` be the active
--   edge set and `S ⊆ A` the active edges with no labelled endpoint.  Small-set
--   mixing bounds the neighbours of `S` that stay in `S`; a local-code distance
--   lower bound forces many neighbours in `A`; and the two unlabelled endpoints
--   allow strictly fewer than `2m` neighbours in `A \ S`.  If the distance beats
--   `2m + lambda`, the bad set `S` is empty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L297-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L297-L367

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.subset_eq_empty_of_internal_expansion_and_external_degree_lt
    [DecidableEq V]
    (M : WeightedGraph V) (radius : Nat) (lambda : ℝ)
    (A S : Finset V) (d m : Nat)
    (hExpand : IsSmallSetEdgeExpanding M radius lambda)
    (hSA : S ⊆ A) (hARadius : A.card ≤ radius)
    (hDegree : HasForwardDegreeAtLeast M S A d)
    (hExternal : ∀ v ∈ S,
      (∑ u ∈ A \ S, M v u) < 2 * m)
    (hThreshold : (2 * m : ℝ) + lambda ≤ d) :
    S = ∅ := by sorry
