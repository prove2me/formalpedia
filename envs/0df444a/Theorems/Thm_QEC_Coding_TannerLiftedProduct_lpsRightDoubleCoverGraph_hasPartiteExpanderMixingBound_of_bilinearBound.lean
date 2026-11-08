-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
-- name    : QEC.Coding.TannerLiftedProduct.lpsRightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:01:03.193287+00:00
-- url     : https://prove2.me/theorems/44911d75-958c-49c8-ab40-43012e5233df
-- title:
--   Tanner Lifted Product: lps Right Double Cover Graph has Partite Expander Mixing Bound of bilinear Bound
-- statement:
--   Specialized spectral-to-double-cover bridge for the concrete LPS family.
--   The only non-elementary input left in this statement is the base Cayley
--   mean-zero bilinear estimate itself.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L289-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L289-L301

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsRightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : SmallSetExpansion.HasMeanZeroBilinearBound
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph (lpsQuaternionFamilyLabel hp hp4 n))
      (lpsQuaternionShell p).card spectral := by sorry
