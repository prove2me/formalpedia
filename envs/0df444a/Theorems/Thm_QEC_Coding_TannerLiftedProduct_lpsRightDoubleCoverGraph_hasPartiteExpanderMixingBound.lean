-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRightDoubleCoverGraph_hasPartiteExpanderMixingBound
-- name    : QEC.Coding.TannerLiftedProduct.lpsRightDoubleCoverGraph_hasPartiteExpanderMixingBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:00:43.194528+00:00
-- url     : https://prove2.me/theorems/fe23ac04-c76c-45ba-850c-6c05f8487376
-- title:
--   Tanner Lifted Product: lps Right Double Cover Graph has Partite Expander Mixing Bound
-- statement:
--   The source's base-Cayley mixing estimate, once proved, transfers directly
--   to the concrete bipartite double cover used by the Tanner product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L273-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L273-L284

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsRightDoubleCoverGraph_hasPartiteExpanderMixingBound
    (hp : p.Prime) (hp4 : p % 4 = 1) (n degree : ℕ)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hMixing : SmallSetExpansion.HasExpanderMixingBound
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
      degree spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph (lpsQuaternionFamilyLabel hp hp4 n))
      degree spectral := by sorry
