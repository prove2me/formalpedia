-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFinRightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
-- name    : QEC.Coding.TannerLiftedProduct.lpsFinRightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:01:53.242445+00:00
-- url     : https://prove2.me/theorems/9caf3a9f-28b3-4d23-b9da-8ff8f6477116
-- title:
--   Tanner Lifted Product: lps Fin Right Double Cover Graph has Partite Expander Mixing Bound of bilinear Bound
-- statement:
--   The spectral-to-double-cover bridge in the exact `Fin (p + 1)`
--   coordinates consumed by the local-code construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L305-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L305-L320

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsFinRightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : SmallSetExpansion.HasMeanZeroBilinearBound
      (rightCayleyGraph
        (lpsFinQuaternionFamilyLabel hp hp4 hCount n)) spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph
        (lpsFinQuaternionFamilyLabel hp hp4 hCount n))
      (p + 1) spectral := by sorry
