-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22LPSFamily_of_fourSqrtBound
-- name    : QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_fourSqrtBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:55:51.981403+00:00
-- url     : https://prove2.me/theorems/bb620d78-bac3-4a3c-a215-4fdc25c2a302
-- title:
--   Tanner Lifted Product: exists pk22 LPSFamily of four Sqrt Bound
-- statement:
--   All coding-theoretic and finite-parameter obligations of the PK22
--   construction, conditional on a `4 √p` LPS spectral estimate.  This is
--   strictly weaker than the optimal Ramanujan bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L120-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L120-L348

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCodeFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22LPSFamilyQubitDecidableEq
set_option maxHeartbeats 1200000

theorem QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_fourSqrtBound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hSpectral : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      SmallSetExpansion.HasMeanZeroBilinearBound
        (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
        (4 * Real.sqrt (p : ℝ))) :
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
