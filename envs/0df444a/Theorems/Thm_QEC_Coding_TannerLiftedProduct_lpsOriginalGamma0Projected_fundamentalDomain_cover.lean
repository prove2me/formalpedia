-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0Projected_fundamentalDomain_cover
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0Projected_fundamentalDomain_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:37:39.681772+00:00
-- url     : https://prove2.me/theorems/73b92f02-e3ea-440c-8084-72cff3b6d9ae
-- title:
--   Tanner Lifted Product: lps Original Gamma0 Projected fundamental Domain cover
-- statement:
--   Fixed original coset representatives really cover the quotient by fundamental-domain images.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L51-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L51-L72

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0Projected_fundamentalDomain_cover (N : ℕ) (τ : ℍ) :
    ∃ (x : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (z : ℍ),
      z ∈ ModularGroup.fd ∧
        lpsOriginalGamma0Projected N (lpsOriginalGamma0CosetRepresentative N x) z=
          (⟦τ⟧ : MulAction.orbitRel.Quotient
            (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := by sorry
