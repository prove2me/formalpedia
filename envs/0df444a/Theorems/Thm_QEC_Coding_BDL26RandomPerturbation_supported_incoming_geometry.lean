-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_supported_incoming_geometry
-- name    : QEC.Coding.BDL26RandomPerturbation.supported_incoming_geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:51:35.805561+00:00
-- url     : https://prove2.me/theorems/da84cdfa-3701-485e-9501-ea3472da58e9
-- title:
--   BDL26 Random Perturbation: supported incoming geometry
-- statement:
--   Source bounds apply to the actual map and the genuinely rounded odd scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingGeometry.lean#L39-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingGeometry.lean#L39-L93

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Sampling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.supported_incoming_geometry (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) {m : ℕ} (hm : 2 ≤ m)
    {lambda : ℝ} (hl : 0 < lambda) (S : OddScale)
    (hscale : (2*(6*(m : ℝ))+1)*lambda ≤ S.ell) (p : Vertex P → Space)
    (hp : ∀ v, p v ∈ displacementCap (6*(m : ℝ)*lambda) (vertexAxis P v)
      (Real.cos (1/(12*(m : ℝ))))) :
    IncomingFaceGeometry P S (perturbedMap P J lambda p)
      (((m : ℝ)-1)*lambda) ((6*(m : ℝ)*widthFactor-1)*lambda) := by sorry
