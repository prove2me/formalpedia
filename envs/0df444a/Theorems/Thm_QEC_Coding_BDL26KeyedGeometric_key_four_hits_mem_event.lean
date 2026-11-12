-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_four_hits_mem_event
-- name    : QEC.Coding.BDL26KeyedGeometric.key_four_hits_mem_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:02:20.136683+00:00
-- url     : https://prove2.me/theorems/e20692cd-3d1e-45de-92ea-5310b9ee1368
-- title:
--   BDL26 Keyed Geometric: key four hits mem event
-- statement:
--   The BDL26 Keyed Geometric construction uses the key four hits mem event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L61-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricAvoidance.lean#L61-L89

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory

theorem QEC.Coding.BDL26KeyedGeometric.key_four_hits_mem_event (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J p : Vertex P → Space)
    (t radius : ℝ) (alpha lambda : ℕ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 1 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ (alpha : ℝ)*lambda) (e : KeyEvent P key hk J radius) (z : Space)
    (hits : ∀ a ∈ e.val,
      (oldTriangleImage P (perturbedMap P J lambda p) a ∩ Metric.closedBall z 1).Nonempty) :
    p ∈ localEvent (keySupport P key hk J radius)
      (keyBad P key hk J radius lambda ((alpha+2)*lambda)) e := by sorry
