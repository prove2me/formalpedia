-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22LPSFamily_of_fourSqrtCenteredThetaCoefficientBound
-- name    : QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_fourSqrtCenteredThetaCoefficientBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:23:33.608113+00:00
-- url     : https://prove2.me/theorems/205134d9-acd8-4604-b7d7-da6408257c0f
-- title:
--   Tanner Lifted Product: exists pk22 LPSFamily of four Sqrt Centered Theta Coefficient Bound
-- statement:
--   Arithmetic `4√p` route to the terminal PK22 family.  The only
--   remaining input is the explicitly stated, relaxed centered theta
--   coefficient estimate; its proof is not supplied by the finite graph and
--   coding-theoretic lemmas.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L539-L571
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L539-L571

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCodeFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22LPSFamilyQubitDecidableEq

theorem QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_fourSqrtCenteredThetaCoefficientBound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hTheta : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      HasFourSqrtCenteredThetaCoefficientBound
        (lpsResiduePrimeSequence hp hp4 n)) :
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
