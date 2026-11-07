-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroBilinearBound_compose
-- name    : QEC.Coding.SmallSetExpansion.HasMeanZeroBilinearBound.compose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:26:17.694695+00:00
-- url     : https://prove2.me/theorems/22d52e8f-b06b-46ef-be90-547f9721be38
-- title:
--   Has Mean Zero Bilinear Bound: compose
-- statement:
--   The two-function spectral estimate for a product of actual symmetric
--   regular adjacency operators, without a distance or expansion conclusion as input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionOperators.lean#L72-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionOperators.lean#L72-L82

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u} [Fintype V]

theorem QEC.Coding.SmallSetExpansion.HasMeanZeroBilinearBound.compose
    {M N : WeightedGraph V} {lambda mu : ℝ} (degreeM degreeN : Nat)
    (hSymmetricM : IsSymmetric M) (hRegularM : IsRegular M degreeM)
    (hSymmetricN : IsSymmetric N) (hRegularN : IsRegular N degreeN)
    (hLambda : 0 ≤ lambda) (hMu : 0 ≤ mu)
    (hM : HasMeanZeroBilinearBound M lambda) (hN : HasMeanZeroBilinearBound N mu) :
    HasMeanZeroBilinearBound (compose M N) (lambda * mu) := by sorry
