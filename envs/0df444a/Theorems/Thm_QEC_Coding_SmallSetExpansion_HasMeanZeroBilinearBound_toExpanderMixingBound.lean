-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroBilinearBound_toExpanderMixingBound
-- name    : QEC.Coding.SmallSetExpansion.HasMeanZeroBilinearBound.toExpanderMixingBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:33:38.792242+00:00
-- url     : https://prove2.me/theorems/e801718d-96d3-47d2-bf6e-9732da1ed56b
-- title:
--   Has Mean Zero Bilinear Bound: to Expander Mixing Bound
-- statement:
--   A two-sided mean-zero spectral bound implies the sharp division-free
--   expander-mixing inequality.  The proof uses centered indicators, so the
--   spectral constant is preserved rather than square-root interpolated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L228-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L228-L299

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.HasMeanZeroBilinearBound.toExpanderMixingBound
    [Fintype V] [DecidableEq V] [Nonempty V]
    {M : WeightedGraph V} {degree : Nat} {spectral : ℝ}
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : HasMeanZeroBilinearBound M spectral) :
    HasExpanderMixingBound M degree spectral := by sorry
