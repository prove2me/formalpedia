-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_HasExpanderMixingBound_toSmallSetEdgeExpanding
-- name    : QEC.Coding.SmallSetExpansion.HasExpanderMixingBound.toSmallSetEdgeExpanding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:45:04.793232+00:00
-- url     : https://prove2.me/theorems/3e1bd3a4-4dbe-49b3-9a92-1fe60582a50b
-- title:
--   Has Expander Mixing Bound: to Small Set Edge Expanding
-- statement:
--   An expander-mixing estimate gives the PK22 small-set bound.  If the
--   uniform-density term obeys `degree * radius / |V| ≤ density`, the resulting
--   mixing constant is `spectral + density`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L304-L346
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L304-L346

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.HasExpanderMixingBound.toSmallSetEdgeExpanding
    [Fintype V] [Nonempty V]
    {M : WeightedGraph V} {degree radius : Nat} {spectral density : ℝ}
    (hMixing : HasExpanderMixingBound M degree spectral)
    (hDensity : (degree : ℝ) * radius ≤ density * Fintype.card V) :
    IsSmallSetEdgeExpanding M radius (spectral + density) := by sorry
