-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_labelledSet_eq_empty
-- name    : QEC.Coding.SmallSetExpansion.labelledSet_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:48:14.184571+00:00
-- url     : https://prove2.me/theorems/c593f1b0-a886-4926-b063-e7ef5fd98b1d
-- title:
--   Small Set Expansion: labelled Set eq empty
-- statement:
--   PK22's labelled-set elimination step. If every labelled vertex expands
--   in at least one of two small-set expanding graphs, and the degree thresholds
--   beat the two mixing constants by a factor of two, then there are no labelled
--   vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L416-L447
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L416-L447

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.labelledSet_eq_empty
    [DecidableEq V]
    (M₁ M₂ : WeightedGraph V)
    (radius₁ radius₂ degree₁ degree₂ : Nat)
    (lambda₁ lambda₂ : ℝ)
    (hLambda₁ : 0 < lambda₁) (hLambda₂ : 0 < lambda₂)
    (hExpand₁ : IsSmallSetEdgeExpanding M₁ radius₁ lambda₁)
    (hExpand₂ : IsSmallSetEdgeExpanding M₂ radius₂ lambda₂)
    (L L₁ L₂ : Finset V)
    (hCover : L ⊆ L₁ ∪ L₂)
    (hL₁ : L₁ ⊆ L) (hL₂ : L₂ ⊆ L)
    (hLRadius₁ : L.card ≤ radius₁)
    (hLRadius₂ : L.card ≤ radius₂)
    (hDegree₁ : HasForwardDegreeAtLeast M₁ L₁ L degree₁)
    (hDegree₂ : HasForwardDegreeAtLeast M₂ L₂ L degree₂)
    (hThreshold₁ : 2 * lambda₁ ≤ degree₁)
    (hThreshold₂ : 2 * lambda₂ ≤ degree₂) :
    L = ∅ := by sorry
