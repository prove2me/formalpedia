-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_preferredCuspCoordinates
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_preferredCuspCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:08:10.121981+00:00
-- url     : https://prove2.me/theorems/a2beae15-ffc3-49f2-bf6a-f87e48b1fa0d
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level preferred Cusp Coordinates
-- statement:
--   Every full higher cusp coordinate maps into the actual lower chart with its genuine power and phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L223-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L223-L269

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_preferredCuspCoordinates
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    let ρ := lpsOriginalCuspRepresentative M c
    let d := lpsOriginalCuspForgetLevel N M hNM c
    ∃ α : ℂ, α ≠ 0 ∧ ‖α‖ = 1 ∧ ∀ q : ℂ,
      q ∈ (lpsOriginalFilledCuspChart M c).target →
      α * q ^ lpsOriginalCuspLevelDegree N M ρ ∈
        (lpsOriginalFilledCuspChart N d).target ∧
      lpsOriginalFilledForgetLevel N M hNM
        ((lpsOriginalFilledCuspChart M c).symm q) =
        (lpsOriginalFilledCuspChart N d).symm
          (α * q ^ lpsOriginalCuspLevelDegree N M ρ) ∧
      lpsOriginalFilledCuspChart N d
        (lpsOriginalFilledForgetLevel N M hNM
          ((lpsOriginalFilledCuspChart M c).symm q)) =
        α * q ^ lpsOriginalCuspLevelDegree N M ρ := by sorry
