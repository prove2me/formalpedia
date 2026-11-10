-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_oldAnchor_mem_triangle
-- name    : QEC.Coding.BDL26RandomPerturbation.oldAnchor_mem_triangle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:03:00.669635+00:00
-- url     : https://prove2.me/theorems/c71ba7a6-33ab-4302-91c7-cbc02514286e
-- title:
--   BDL26 Random Perturbation: old Anchor mem triangle
-- statement:
--   Every old anchor lies in its own actual triangle, including collapsed labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L50-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L50-L54

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.oldAnchor_mem_triangle (P : TannerSquarePresentation) (J : Vertex P → Space)
    (a : Triangle P) :
    oldAnchor P J a ∈ oldTriangleImage P (fun v => (1/2 : ℝ) • J v) a := by sorry
