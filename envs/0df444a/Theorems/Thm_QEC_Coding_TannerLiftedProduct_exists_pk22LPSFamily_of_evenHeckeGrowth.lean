-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22LPSFamily_of_evenHeckeGrowth
-- name    : QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_evenHeckeGrowth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:00:46.216537+00:00
-- url     : https://prove2.me/theorems/f874a7a7-9533-46a8-b2b1-5df08c012629
-- title:
--   Tanner Lifted Product: exists pk22 LPSFamily of even Hecke Growth
-- statement:
--   Hecke-growth form of the terminal LPS assembly.  The finite-dimensional
--   trace endgame is fully discharged: it is enough to bound every even Hecke
--   evaluation at every exponential rate strictly above `√p`; the sharp
--   Ramanujan interval and hence the PK22 qLDPC family follow.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L474-L503
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L474-L503

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCodeFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRightCayleyGraph_isSymmetric

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22LPSFamilyQubitDecidableEq

theorem QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_evenHeckeGrowth
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hHeckeGrowth : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
      (n : ℕ)
      (i : Fin (Module.finrank ℂ
        (EuclideanSpace ℂ (LPSVertexGroup hp hp4 n))))
      (t : ℝ), Real.sqrt (p : ℝ) < t →
      (fun m : ℕ =>
        (lpsHeckePolynomial ℝ (p : ℝ) (2 * m)).eval
          ((SmallSetExpansion.centeredAdjacencyEuclidean_isSymmetric
            (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) (p + 1)
            (lpsRightCayleyGraph_isSymmetric hp hp4 n)).eigenvalues rfl i))
        =O[Filter.atTop] fun m : ℕ => t ^ (2 * m)) :
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
