-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalNumerator_germ_identity
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalNumerator_germ_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:27:57.703394+00:00
-- url     : https://prove2.me/theorems/a374dedc-14f6-43d5-9212-77fcfaf17df1
-- title:
--   Tanner Lifted Product: lps Original Reciprocal Numerator germ identity
-- statement:
--   The constructed modular numerator equals E4 cube power times the original function in genuine germs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNumerator.lean#L152-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNumerator.lean#L152-L196

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalNumerator_germ_identity
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (k : ℕ)
    (hi : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
        0 ≤ meromorphicOrderAt
          ((lpsOriginalReciprocalClearedRepresentative N hN F hF k).val ∘
            (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
          (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x))) :
    let A := lpsOriginalReciprocalNumeratorModularForm N hN F hF hc k hi
    lpsOriginalHolomorphicToMeromorphicGerm
      (lpsOriginalLevelFormHolomorphic N k A) =
      lpsOriginalHolomorphicToMeromorphicGerm (lpsOriginalE4PowerHolomorphic k) *
        (lpsOriginalFilledMeromorphicRestriction N hN F hF).val := by sorry
