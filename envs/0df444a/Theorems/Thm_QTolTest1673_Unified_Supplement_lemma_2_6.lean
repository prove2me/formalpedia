-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_lemma_2_6
-- name    : QTolTest1673.Unified.Supplement.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:23:50.198138+00:00
-- url     : https://prove2.me/theorems/321e569f-5825-4bcc-a6c3-7044350668b8
-- title:
--   Lemma 2.6 — Mass testing for M candidate sets
-- statement:
--   Mass testing for M candidate sets: with 0≤b<a≤1, γ=a−b, 0<δ<1, m ≥ (8/γ²)ln(2M/δ) i.i.d. samples from P suffice to distinguish max_V P(V) ≥ a from max_V P(V) ≤ b with error at most δ.
--
--   $$m\ge\frac8{(a-b)^2}\ln\frac{2M}{\delta}\quad\Longrightarrow\quad\Pr[\text{correct output on either mass promise}]\ge1-\delta.$$
--
--   The candidate family is nonempty, its sets are measurable, and the rule accepts exactly when some empirical mass is at least (a+b)/2. The YES promise is that some candidate has mass at least a; the NO promise is that all have mass at most b. The source parameters satisfy 0≤b<a≤1 and 0<δ<1.
--
--   This result supplies a supporting statement for Theorem 6.1.
--
--   Differences from the source:
--   - encoding: a probability distribution and candidate sets on a ground set → a probability measure on an arbitrary measurable space, with measurable candidates and product sample law; reason: measurability is the usual implicit probability convention; there is no finite-ground or discrete-law restriction
--   - encoding: a sample suffices to distinguish the two mass promises → the empirical-midpoint rule accepts or rejects with probability at least 1−δ; reason: this is the explicit decision rule and guarantee of the proof on p.17
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Lemma 2.6, p. 17

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Lemma 2.6, p.17: the stated empirical-midpoint rule, on any measurable ground space. -/
theorem lemma_2_6 {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (F : Finset (Set X)) (hF : F.Nonempty) (hmeas : ∀ V ∈ F, MeasurableSet V)
    (a b δ : ℝ) (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ 1)
    (hδ : 0 < δ) (hδ' : δ < 1) (m : ℕ)
    (hm : (8/(a-b)^2)*Real.log (2*(F.card : ℝ)/δ) ≤ m) :
  let accept : Set (Fin m → X) := {x | ∃ V ∈ F,
    (a+b)/2 ≤ (m : ℝ)⁻¹ * ∑ i, if x i ∈ V then (1 : ℝ) else 0}
  ((∃ V ∈ F, a ≤ P.real V) →
    1-δ ≤ (Measure.pi (fun _ : Fin m => P)).real accept) ∧
  ((∀ V ∈ F, P.real V ≤ b) →
    1-δ ≤ (Measure.pi (fun _ : Fin m => P)).real acceptᶜ) := by sorry

end QTolTest1673.Unified.Supplement
