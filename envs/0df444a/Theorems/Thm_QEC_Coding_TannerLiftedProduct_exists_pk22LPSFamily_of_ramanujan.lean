-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22LPSFamily_of_ramanujan
-- name    : QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_ramanujan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:01:04.937784+00:00
-- url     : https://prove2.me/theorems/1c6e724d-fbba-4753-bd41-918f30ab78d9
-- title:
--   Tanner Lifted Product: exists pk22 LPSFamily of ramanujan
-- statement:
--   The original Ramanujan interface remains available: its optimal
--   `2 √p` estimate implies the weaker `4 √p` estimate used by the concrete
--   PK22 parameter schedule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L353-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L353-L379

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCodeFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22LPSFamilyQubitDecidableEq

theorem QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_ramanujan
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hRamanujan : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      SmallSetExpansion.HasMeanZeroBilinearBound
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
