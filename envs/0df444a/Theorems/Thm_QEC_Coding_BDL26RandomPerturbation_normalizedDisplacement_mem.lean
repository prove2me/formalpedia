-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_normalizedDisplacement_mem
-- name    : QEC.Coding.BDL26RandomPerturbation.normalizedDisplacement_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:49:23.474163+00:00
-- url     : https://prove2.me/theorems/89d16647-3f33-4813-b390-08ca2f32a606
-- title:
--   BDL26 Random Perturbation: normalized Displacement mem
-- statement:
--   The BDL26 Random Perturbation construction uses the normalized Displacement mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L20-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L20-L27

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.normalizedDisplacement_mem (p : Space) {R c : ℝ} (hR : 0 < R) (u : Sphere)
    (hp : p ∈ displacementCap R u c) : normalizedDisplacement p hR hp.1 ∈ cap u c := by sorry
