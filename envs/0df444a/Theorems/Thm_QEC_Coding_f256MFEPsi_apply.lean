-- Prove2me | Theorems.Thm_QEC_Coding_f256MFEPsi_apply
-- name    : QEC.Coding.f256MFEPsi_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:40.457669+00:00
-- url     : https://prove2.me/theorems/e3d85521-2c63-43b9-b0e9-5b8324048620
-- title:
--   Coding: f256 MFEPsi apply
-- statement:
--   Evaluation of the contraction map on a coordinate vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L92-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L92-L96

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFEPsi_apply (v : Fin 512 → ZMod 2) :
    f256MFEPsi v =
      ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
        v (f256MFEIndex i j k) •
          (f256PolynomialBasis i * f256PolynomialBasis j * f256PolynomialBasis k) := by sorry
