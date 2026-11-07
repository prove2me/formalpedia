-- Prove2me | Theorems.Thm_UncrowdedColoring_theorem_3_3
-- name    : UncrowdedColoring.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:13:55.360477+00:00
-- url     : https://prove2.me/theorems/5d2d979b-a0d1-470c-a3ef-8ad7130ec379
-- title:
--   Theorem 3.3 — Lovász Local Lemma, asymmetric version
-- statement:
--   Let $A_1,\dots,A_n$ be events in a probability space, and for each $i$ let $D_i\subseteq[n]\setminus\{i\}$ be such that $A_i$ is mutually independent of $\{A_j:j\notin D_i\cup\{i\}\}$. If $\mathbb P(A_i)\le 1/4$ and $\sum_{j\in D_i}\mathbb P(A_j)\le 1/4$ for all $i$, then
--   $$\mathbb P\Big(\bigcap_i A_i^{\mathrm c}\Big)>0.$$
--
--   This form finishes the coloring in Lemma 4.8.
--
--   **Formalization Note** Mutual independence is independence from the generated σ-algebra.
--
--   Differences from the source:
--   - encoding: A_i mutually independent of {A_j : j ∉ D_i ∪ {i}} → Indep of generateFrom {A i} and generateFrom (A '' {j | j ∉ D i ∧ j ≠ i}), with the events measurable; reason: the standard meaning of mutual independence
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Theorem 3.3, p.14

import Mathlib

open MeasureTheory ProbabilityTheory

namespace UncrowdedColoring

/-- **Theorem 3.3 (Lovász Local Lemma, asymmetric version)**, p.14.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Theorem 3.3, p.14.

**Formalization Note.** A general probability space with measurable events. "`A_i` is mutually
independent of `{A_j : j ∉ D_i ∪ {i}}`" is independence of `A_i` from the σ-algebra those events
generate. -/
theorem theorem_3_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (D : Fin n → Finset (Fin n)) (hD : ∀ i, i ∉ D i)
    (hind : ∀ i, Indep (MeasurableSpace.generateFrom {A i})
      (MeasurableSpace.generateFrom (A '' {j | j ∉ D i ∧ j ≠ i})) μ)
    (h₁ : ∀ i, μ.real (A i) ≤ 1 / 4)
    (h₂ : ∀ i, ∑ j ∈ D i, μ.real (A j) ≤ 1 / 4) :
    0 < μ (⋂ i, (A i)ᶜ) := by sorry

end UncrowdedColoring
