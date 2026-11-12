-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_native_commuting_mask_escapes_ae
-- name    : QEC.Coding.BDL26RXIncidenceHullGeometry.native_commuting_mask_escapes_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T12:44:33.979842+00:00
-- url     : https://prove2.me/theorems/d17c652c-537f-4daa-abad-cc271b1ec3f5
-- title:
--   BDL26 RXIncidence Hull Geometry: native commuting mask escapes ae
-- statement:
--   All commuting masks and centres are simultaneous under the original law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L103-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L103-L117

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGeometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open BDL26RXDifferentialMasks BDL26RXIncidenceHullRetainedGrowth
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RXIncidenceHullGeometry.native_commuting_mask_escapes_ae {L : ℝ} (p : GeometricParameters L) (R : ℝ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (hullLevel (ballBudget p.t R)+1),
      ∀ (A : Finset (state (perturbationOddScale p) (hullLevel (ballBudget p.t R))).presentation.Q)
    (B : Finset (FamilyZ (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
      (hullStep (ballBudget p.t R)).succ))
    (hseed : seed (perturbationOddScale p) (hullLevel (ballBudget p.t R)) ⊆ A)
    (commutes : ∀ w, maskWord B
      (nativeDifferential (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1) (hullStep (ballBudget p.t R)) w) =
      nativeDifferential (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
        (hullStep (ballBudget p.t R)) (maskWord A w)) (center : Space),
    ∃ q ∈ A, R < dist
      (BDL26NativeFiniteComposition.history p (hullLevel (ballBudget p.t R)+1) z
        ⟨hullLevel (ballBudget p.t R),by omega⟩ (.q q)) center := by sorry
