-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_wordPairing_transposeC0Word
-- name    : QEC.Coding.TannerLiftedProduct.wordPairing_transposeC0Word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:43.83896+00:00
-- url     : https://prove2.me/theorems/3afd7571-80ab-40cf-98de-44d7a5858378
-- title:
--   Tanner Lifted Product: word Pairing transpose C0 Word
-- statement:
--   The Tanner Lifted Product construction uses the word Pairing transpose C0 Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L649-L660
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L649-L660

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq F] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.wordPairing_transposeC0Word
    (inverseDirection : W ≃ W)
    (x : Word F (LiftedProduct.C0Index (Fin 2 × R) W G))
    (y : Word F (LiftedProduct.C2Index W (Fin 2 × R) G)) :
    wordPairing (transposeC0Word inverseDirection x) y =
      wordPairing x
        (fun c0 => y ((transposeEdgeEquiv inverseDirection.symm).symm c0)) := by sorry
