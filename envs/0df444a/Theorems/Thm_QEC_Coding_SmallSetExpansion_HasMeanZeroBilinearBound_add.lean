-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroBilinearBound_add
-- name    : QEC.Coding.SmallSetExpansion.HasMeanZeroBilinearBound.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:35:27.704267+00:00
-- url     : https://prove2.me/theorems/acc13a48-0adb-434d-8829-04eb73826c40
-- title:
--   Has Mean Zero Bilinear Bound: add
-- statement:
--   Spectral constants add under a weighted graph union.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionOperators.lean#L39-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionOperators.lean#L39-L49

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u} [Fintype V]

theorem QEC.Coding.SmallSetExpansion.HasMeanZeroBilinearBound.add
    {M N : WeightedGraph V} {lambda mu : ℝ}
    (hM : HasMeanZeroBilinearBound M lambda) (hN : HasMeanZeroBilinearBound N mu) :
    HasMeanZeroBilinearBound (add M N) (lambda + mu) := by sorry
