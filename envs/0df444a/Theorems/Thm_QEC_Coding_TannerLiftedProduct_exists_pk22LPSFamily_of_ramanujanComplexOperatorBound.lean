-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22LPSFamily_of_ramanujanComplexOperatorBound
-- name    : QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_ramanujanComplexOperatorBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:55:56.127785+00:00
-- url     : https://prove2.me/theorems/dbc6190f-321d-4a93-b3c6-4cdde0ab078c
-- title:
--   Tanner Lifted Product: exists pk22 LPSFamily of ramanujan Complex Operator Bound
-- statement:
--   Complex operator-norm form of the terminal LPS assembly.  This removes
--   the final real/complex mismatch between the unitary regular representation
--   and the graph-expansion API.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L415-L436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L415-L436

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCodeFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22LPSFamilyQubitDecidableEq

theorem QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_ramanujanComplexOperatorBound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hRamanujan : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      SmallSetExpansion.HasMeanZeroComplexOperatorBound
        (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
        (2 * Real.sqrt (p : ℝ))) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one
        a.prime a.oneModFour
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') ∧
        QEC.QLDPC.HasEventualRateAtLeast
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by sorry
