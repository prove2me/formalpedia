-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsE2DifferenceThetaBasis
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsE2DifferenceThetaBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:48.027103+00:00
-- url     : https://prove2.me/theorems/1957a64e-942d-4ff2-8f02-f27e5a5b4b3c
-- title:
--   Tanner Lifted Product: coeff q Expansion lps E2 Difference Theta Basis
-- statement:
--   The Tanner Lifted Product construction uses the coeff q Expansion lps E2 Difference Theta Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L283-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean#L283-L287

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsE2DifferenceThetaBasis (q : ℕ) [Fact q.Prime]
    (a : Fin 5) (b : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsE2DifferenceThetaBasis q a b))=
      lpsE2DifferenceCoefficient (2^a.val*q^b.val) n := by sorry
