-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroOperatorBound_toBilinearBound
-- name    : QEC.Coding.SmallSetExpansion.HasMeanZeroOperatorBound.toBilinearBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:37:48.15097+00:00
-- url     : https://prove2.me/theorems/bc9a41b9-cdcc-4749-90eb-f453da92bc3b
-- title:
--   Has Mean Zero Operator Bound: to Bilinear Bound
-- statement:
--   An `ℓ²` adjacency-operator bound implies the two-function bilinear bound
--   used by expander mixing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L328-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L328-L367

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.HasMeanZeroOperatorBound.toBilinearBound
    [Fintype V]
    {M : WeightedGraph V} {spectral : ℝ}
    (hSpectralNonnegative : 0 ≤ spectral)
    (hOperator : HasMeanZeroOperatorBound M spectral) :
    HasMeanZeroBilinearBound M spectral := by sorry
