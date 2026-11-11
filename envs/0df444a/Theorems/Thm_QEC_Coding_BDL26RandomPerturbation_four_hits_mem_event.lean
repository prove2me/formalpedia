-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_four_hits_mem_event
-- name    : QEC.Coding.BDL26RandomPerturbation.four_hits_mem_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:07:30.116167+00:00
-- url     : https://prove2.me/theorems/3a0ad038-e9af-4bdb-99eb-759d311d817c
-- title:
--   BDL26 Random Perturbation: four hits mem event
-- statement:
--   The BDL26 Random Perturbation construction uses the four hits mem event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NetCatch.lean#L10-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NetCatch.lean#L10-L37

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_HitGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NetCatch
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.four_hits_mem_event (P : TannerSquarePresentation) (J p : Vertex P → Space)
    (t radius : ℝ) (alpha lambda : ℕ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 1 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ (alpha : ℝ)*lambda) (e : Event P J radius) (z : Space)
    (hits : ∀ a ∈ e.val,
      (oldTriangleImage P (perturbedMap P J lambda p) a ∩ Metric.closedBall z 1).Nonempty) :
    p ∈ localEvent (eventSupport P J radius)
      (eventBad P J radius lambda ((alpha+2)*lambda)) e := by sorry
