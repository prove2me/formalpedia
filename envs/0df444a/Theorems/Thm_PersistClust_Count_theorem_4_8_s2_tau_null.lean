-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_8_s2_tau_null
-- name    : PersistClust.Count.theorem_4_8_s2_tau_null
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T15:11:21.713985+00:00
-- url     : https://prove2.me/theorems/4557009e-dcd0-42b4-a1e8-5b2d1f7c9f3e
-- title:
--   Theorem 4.8 shell — S2: the tau-level null event (conditional form)
-- statement:
--   For a measurable density f on a measure space with n i.i.d. samples, the event that some sample point lies exactly on the tau-level set {x | f x = tau} is null, CONDITIONAL on the tau-level set itself being mu-null: sampleMeasure mu n f {pts | exists i, f (pts i) = tau} = 0 given mu {x | f x = tau} = 0. This is the tau-avoidance step of the probabilistic shell of Theorem 4.8 (persistence-based clustering). The conditional form is sharp: the plateau-density analysis showed the hypothesis cannot be dropped (a density equal to tau on a positive-measure set makes the sample hit the level with positive probability), which is why the corrected Theorem 4.8 (theorem_4_8_corrected) carries mu {x | f x = tau} = 0 as an explicit hypothesis. Companion of the accepted shell lemma theorem_4_8_s1_pos_null; together they discharge the sample-avoidance steps of the shell assembly.
-- source:
--   Formalization of the tau-avoidance step in the proof of Theorem 4.8, Persistence-Based Clustering in Riemannian Manifolds (rr/6968), in the conditional form established by the plateau-density obstruction. Child of the corrected root theorem_4_8_corrected (id 6b9ad4c5-ed11-4695-b810-2a1269327d27) whose htaunull hypothesis is exactly this lemma's hypothesis; sibling of the accepted theorem_4_8_s1_pos_null (id e1665ca1).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold ENNReal

namespace PersistClust.Count

theorem theorem_4_8_s2_tau_null {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (n : ℕ)
    (τ : ℝ) (hdens : IsDensity μ f) (hf : Measurable f) (hτnull : μ {x : X | f x = τ} = 0) :
    sampleMeasure μ n f {pts : Fin n → X | ∃ i : Fin n, f (pts i) = τ} = 0
    := by sorry
