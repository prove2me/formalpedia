-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add
-- name    : QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:47:31.53721+00:00
-- url     : https://prove2.me/theorems/267aa875-bbe0-4086-b4c8-5d30fb60b4c3
-- title:
--   Is Small Set Edge Expanding: add
-- statement:
--   A union on the same vertices has the sum of the two mixing constants.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L91-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L91-L103

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.add
    {M N : WeightedGraph V} {radius : Nat} {lambda mu : ℝ}
    (hM : IsSmallSetEdgeExpanding M radius lambda)
    (hN : IsSmallSetEdgeExpanding N radius mu) :
    IsSmallSetEdgeExpanding (add M N) radius (lambda + mu) := by sorry
