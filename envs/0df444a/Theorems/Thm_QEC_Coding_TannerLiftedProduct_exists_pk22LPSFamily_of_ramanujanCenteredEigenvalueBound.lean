-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22LPSFamily_of_ramanujanCenteredEigenvalueBound
-- name    : QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_ramanujanCenteredEigenvalueBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:00:11.814033+00:00
-- url     : https://prove2.me/theorems/e142de15-af79-4ecf-a7db-0297c4a6c59b
-- title:
--   Tanner Lifted Product: exists pk22 LPSFamily of ramanujan Centered Eigenvalue Bound
-- statement:
--   Eigenvalue form of the terminal LPS assembly.  The constant mode is
--   removed explicitly, so the only remaining external input is the usual
--   Ramanujan bound on the centered LPS adjacency spectrum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L441-L468
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGoodFamilyAssembly.lean#L441-L468

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

theorem QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_ramanujanCenteredEigenvalueBound
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hRamanujan : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
      (i : Fin (Module.finrank ℂ
        (EuclideanSpace ℂ (LPSVertexGroup hp hp4 n)))),
      |(SmallSetExpansion.centeredAdjacencyEuclidean_isSymmetric
          (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) (p + 1)
          (lpsRightCayleyGraph_isSymmetric hp hp4 n)).eigenvalues rfl i| ≤
        2 * Real.sqrt (p : ℝ)) :
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
