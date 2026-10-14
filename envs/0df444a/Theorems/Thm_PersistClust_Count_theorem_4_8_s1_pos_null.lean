-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_8_s1_pos_null
-- name    : PersistClust.Count.theorem_4_8_s1_pos_null
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T13:29:17.152114+00:00
-- url     : https://prove2.me/theorems/e1665ca1-f9ed-4f1a-9620-37757988decd
-- title:
--   Theorem 4.8 shell — S1: the sample-positivity null event
-- statement:
--   For a measurable density f on a measure space with n i.i.d. samples, the event that some sample point fails to be strictly positive is null: sampleMeasure mu n f {pts | exists i, f (pts i) <= 0} = 0. This is the positivity step of the probabilistic shell of Theorem 4.8 (persistence-based clustering): it discharges the hypothesis hpos of the accepted core (theorem_4_8_core, id 027bdb99) almost surely.
-- source:
--   Formalization of the sample-positivity step in the proof of Theorem 4.8, Persistence-Based Clustering in Riemannian Manifolds (rr/6968). Child of theorem_4_8 (id 8f14d99e-9520-4f95-a91a-167ff27ea090); sibling of the accepted core.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold

namespace PersistClust.Count

/-! ## S1 — the sample-positivity null set of the 4.8 probabilistic shell

The accepted core (`PersistClust.Count.theorem_4_8_core`, id 027bdb99) takes the
deterministic positivity hypothesis `hpos : ∀ i : Fin n, 0 < f (pts i)`.  The shell
must show that its failure set `{pts | ∃ i, f (pts i) ≤ 0}` (note: `¬(0 < f (pts i))`
unfolds to `f (pts i) ≤ 0`) is `sampleMeasure`-null.

Only three facts are used: the density normalization `IsDensity μ f` (non-negativity AND
`∫ f dμ = 1` — the latter only to make `sampleLaw μ f` a probability measure, hence
sigma-finite, which `Measure.pi_eval_preimage_null` needs) and measurability of `f`
(in the root it follows from `hLip` via Lipschitz → continuous → measurable, using
`[BorelSpace X]`).  On the level set `{x | f x ≤ 0}` non-negativity forces `f = 0`, so
the density integrand `ENNReal.ofReal ∘ f` vanishes there and each one-coordinate slice
has `sampleLaw μ f {x | f x ≤ 0} = 0`.
`Measure.pi_eval_preimage_null` transports the null slice to the product, and
`measure_iUnion_null_iff` finishes the finite union. -/

theorem theorem_4_8_s1_pos_null {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (n : ℕ)
    (hdens : IsDensity μ f) (hf : Measurable f) :
    sampleMeasure μ n f {pts : Fin n → X | ∃ i : Fin n, f (pts i) ≤ 0} = 0 := by sorry
