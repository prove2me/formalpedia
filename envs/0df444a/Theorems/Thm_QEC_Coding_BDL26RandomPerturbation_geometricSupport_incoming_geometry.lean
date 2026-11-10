-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricSupport_incoming_geometry
-- name    : QEC.Coding.BDL26RandomPerturbation.geometricSupport_incoming_geometry
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:19:09.379175+00:00
-- url     : https://prove2.me/theorems/980e2149-9116-4de3-92ab-9fc341c7783c
-- title:
--   BDL26 Random Perturbation: geometric Support incoming geometry
-- statement:
--   Every actual supported assignment has the source side, diagonal and three width bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L77-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L77-L88

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AvoidanceDensity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.geometricSupport_incoming_geometry (P : TannerSquarePresentation)
    (J : Vertex P → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (S : OddScale)
    (hscale : (2*(6*(p.m : ℝ))+1)*(p.lambda : ℝ) ≤ S.ell)
    (w : Vertex P → Space) (hw : w ∈ geometricSupport P p) :
    IncomingFaceGeometry P S (perturbedMap P J p.lambda w)
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) := by sorry
