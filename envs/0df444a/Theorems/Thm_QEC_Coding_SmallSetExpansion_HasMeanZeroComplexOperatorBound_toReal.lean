-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroComplexOperatorBound_toReal
-- name    : QEC.Coding.SmallSetExpansion.HasMeanZeroComplexOperatorBound.toReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:36:44.537214+00:00
-- url     : https://prove2.me/theorems/06b883c4-5631-439f-a2e7-24a066a6f2ae
-- title:
--   Has Mean Zero Complex Operator Bound: to Real
-- statement:
--   A complex adjacency-operator bound restricts to the real mean-zero
--   subspace without changing its spectral constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L100-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L100-L109

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.HasMeanZeroComplexOperatorBound.toReal
    [Fintype V]
    {M : WeightedGraph V} {spectral : ℝ}
    (hComplex : HasMeanZeroComplexOperatorBound M spectral) :
    HasMeanZeroOperatorBound M spectral := by sorry
