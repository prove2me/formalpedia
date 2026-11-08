-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHeckePairing_gamma0Domain
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_gamma0Domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:56:42.814706+00:00
-- url     : https://prove2.me/theorems/9419df7a-7f84-4d79-bb34-1a0a55cbb6a7
-- title:
--   Tanner Lifted Product: lps Cusp Hecke Pairing gamma0 Domain
-- statement:
--   Every actual Gamma0 domain computes the original genuine Hecke pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L17-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L17-L23

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_gamma0Domain (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      ∫τ in s,petersson 2 (lpsHeckeSlashSum p f) g τ := by sorry
