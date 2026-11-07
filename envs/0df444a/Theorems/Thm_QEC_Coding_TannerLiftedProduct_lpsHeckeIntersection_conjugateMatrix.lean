-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_conjugateMatrix
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_conjugateMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:21.300313+00:00
-- url     : https://prove2.me/theorems/3ca7369c-3df2-45bd-b8c9-a25776ac76bf
-- title:
--   Tanner Lifted Product: lps Hecke Intersection conjugate Matrix
-- statement:
--   The actual infinity representative conjugates Gamma0(Np) to an integral Gamma0(N) matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L16-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L16-L36

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_conjugateMatrix (N p : ℕ) [Fact p.Prime]
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N*p)) :
    ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p none * (γ:Matrix (Fin 2) (Fin 2) ℤ) =
        (δ:Matrix (Fin 2) (Fin 2) ℤ) * lpsHeckeUpperMatrix p none := by sorry
