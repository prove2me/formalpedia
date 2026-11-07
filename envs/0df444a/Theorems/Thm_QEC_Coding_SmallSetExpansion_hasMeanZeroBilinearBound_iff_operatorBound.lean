-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_hasMeanZeroBilinearBound_iff_operatorBound
-- name    : QEC.Coding.SmallSetExpansion.hasMeanZeroBilinearBound_iff_operatorBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:18:46.815905+00:00
-- url     : https://prove2.me/theorems/daf7fefb-78d6-4906-b83e-5cbcb788b498
-- title:
--   Small Set Expansion: has Mean Zero Bilinear Bound iff operator Bound
-- statement:
--   For a symmetric regular finite graph, the bilinear and adjacency
--   operator-norm formulations of the mean-zero spectral estimate are
--   equivalent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L403-L446
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L403-L446

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.hasMeanZeroBilinearBound_iff_operatorBound
    [Fintype V]
    {M : WeightedGraph V} {degree : Nat} {spectral : ℝ}
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree)
    (hSpectralNonnegative : 0 ≤ spectral) :
    HasMeanZeroBilinearBound M spectral ↔
      HasMeanZeroOperatorBound M spectral := by sorry
