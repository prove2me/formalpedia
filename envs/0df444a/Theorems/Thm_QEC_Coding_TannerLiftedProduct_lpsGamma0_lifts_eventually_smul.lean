-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_lifts_eventually_smul
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0_lifts_eventually_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:50:24.415465+00:00
-- url     : https://prove2.me/theorems/c83eafcd-0327-4714-bd9a-2ceb7e751ce2
-- title:
--   Tanner Lifted Product: lps Gamma0 lifts eventually smul
-- statement:
--   Genuine continuous local lifts differ near a point by ONE original Mobius representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0Quotient.lean#L111-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0Quotient.lean#L111-L141

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Geometry.Manifold.Instances.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0_lifts_eventually_smul (N : ℕ) [NeZero N] (hN : 4∣N)
    {X : Type*} [TopologicalSpace X] (u v : X→ℍ) (x : X)
    (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (he : (fun z => Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) (v z)) =ᶠ[𝓝 x]
      (fun z => Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) (u z))) :
    ∃ γ : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      v =ᶠ[𝓝 x] (fun z => γ.val • u z) := by sorry
