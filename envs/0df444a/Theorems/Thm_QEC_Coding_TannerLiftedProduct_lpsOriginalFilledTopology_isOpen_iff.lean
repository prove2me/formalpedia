-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_isOpen_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_isOpen_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:39:25.524774+00:00
-- url     : https://prove2.me/theorems/9b753e86-5ccc-4589-9018-33c42b1f6b6a
-- title:
--   Tanner Lifted Product: lps Original Filled Topology is Open iff
-- statement:
--   Openness in the actual gluing topology is tested on the true interior and true filled discs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L31-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L31-L42

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_isOpen_iff (N : ℕ) [NeZero N]
    (s : Set (LPSOriginalFilledCurve N)) :
    IsOpen[lpsOriginalFilledTopology N] s ↔
      IsOpen ((Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) ⁻¹' s) ∧
        ∀ c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
          IsOpen (lpsOriginalFilledCuspParam N c ⁻¹' s) := by sorry
