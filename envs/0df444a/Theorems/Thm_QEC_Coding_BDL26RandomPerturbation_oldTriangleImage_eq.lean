-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_oldTriangleImage_eq
-- name    : QEC.Coding.BDL26RandomPerturbation.oldTriangleImage_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:34:31.592625+00:00
-- url     : https://prove2.me/theorems/b881bb51-ce07-47a7-b692-d19713a4fe49
-- title:
--   BDL26 Random Perturbation: old Triangle Image eq
-- statement:
--   The actual three-coordinate convex hull, including degenerate maps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Incidence.lean#L28-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Incidence.lean#L28-L34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding

theorem QEC.Coding.BDL26RandomPerturbation.oldTriangleImage_eq (P : TannerSquarePresentation) (t : Triangle P)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (J : Vertex P → E) :
    oldTriangleImage P J t = convexHull ℝ (Set.range fun i => J (triangleVertex P t i)) := by sorry
