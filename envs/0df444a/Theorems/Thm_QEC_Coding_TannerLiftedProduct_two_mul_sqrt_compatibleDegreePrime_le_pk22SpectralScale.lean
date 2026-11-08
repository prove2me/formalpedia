-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_sqrt_compatibleDegreePrime_le_pk22SpectralScale
-- name    : QEC.Coding.TannerLiftedProduct.two_mul_sqrt_compatibleDegreePrime_le_pk22SpectralScale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:29:45.708205+00:00
-- url     : https://prove2.me/theorems/79fcef37-2702-4fc4-a4e9-4310480359ff
-- title:
--   Tanner Lifted Product: two mul sqrt compatible Degree Prime le pk22 Spectral Scale
-- statement:
--   The Ramanujan scale `2 √p` of any compatible prime degree is bounded
--   by the concrete spectral schedule whenever its replication count lies below
--   `64 x⁶`.  This is the arithmetic bridge from the LPS eigenvalue theorem to
--   the deterministic PK22 local-code thresholds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L407-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L407-L439

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.two_mul_sqrt_compatibleDegreePrime_le_pk22SpectralScale
    (q t x : Nat)
    (a : CompatibleDegreePrime (pk22LocalWidth q t))
    (hUpper : a.blocks ≤ 64 * x ^ 6) :
    2 * Real.sqrt (a.p : ℝ) ≤
      ((pk22SpectralCoefficient q t * x ^ 3 : Nat) : ℝ) := by sorry
