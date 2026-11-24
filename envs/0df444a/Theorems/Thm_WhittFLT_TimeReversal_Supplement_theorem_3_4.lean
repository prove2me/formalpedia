-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_theorem_3_4
-- name    : WhittFLT.TimeReversal.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:46:45.066661+00:00
-- url     : https://prove2.me/theorems/14a346f0-fdc7-4ad1-9d80-13b5f45ec4d5
-- title:
--   Theorem 3.4 (companion theorem; not used in the proof of the goal) — random time changes (corrected)
-- statement:
--   Let $T_1,T_2,T_3$ be real intervals, $T_1$ open at both ends, $T_2\subseteq T_3$, and $S$ a complete separable metric space. Let $(X_n,Y_n)$ be random elements of $D(T_3,S)\times D_0(T_1,T_2)$ and let $y$ be a deterministic continuous strictly increasing element of $D_0(T_1,T_2)$. Suppose the laws of $X_n|_{y(T_1)}$ are relatively compact, $Y_n\Rightarrow y$, and the finite-dimensional laws of $X_n\circ Y_n$ converge for every finite tuple in some dense subset of $T_1$. There is one random element $Z$ such that
--
--   $$X_n\circ Y_n\Rightarrow Z\quad\text{in }D(T_1,S),\qquad X_n|_{y(T_1)}\Rightarrow Z\circ y^{-1}\quad\text{in }D(y(T_1),S).$$
--
--   The same $Z$ occurs in both conclusions. The statement also certifies that the bundled composition and inverse-composition maps give the prescribed pointwise values.
--
--   **Formalization Note** Joint laws replace random variables on possibly different probability spaces; $Z$ is realized by the identity on its limiting path-law space. The sentence before the theorem requires the right end of $T_1$ to be open. The correction also opens the left end: for $T_1=[0,1)$, $Y_n=e-1/n$ and $X_n=5\mathbf1_{[-1/n,0)}$ satisfy the printed assumptions, while $X_n\circ Y_n=5\mathbf1_{[0,1/n)}$ has no $J_1$ limit. This mirrors Bauer's endpoint obstruction.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
--   - correction: T₁ is required to be open on the right. → Require T₁ to be open at both ends.; reason: A shrinking spike at a closed left endpoint satisfies the printed assumptions but prevents J₁ convergence.
--   - encoding: Random elements on potentially different probability spaces. → Arbitrary joint probability laws and one common limiting path law.; reason: Every random element has its joint law, and each probability law is realized by the identity random element.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Theorem 3.4, p. 77 (PDF 11)

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Supplement_Operations

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem theorem_3_4 {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (T₁ T₂ T₃ : Set ℝ) (hT₁ : T₁.OrdConnected) (hT₂ : T₂.OrdConnected)
    (hT₃ : T₃.OrdConnected) (hopen : IsOpen T₁) (h₂₃ : T₂ ⊆ T₃)
    (y : D0 T₁ T₂) (hycont : Continuous y.1.1) (hystrict : StrictMono y.1.1)
    (ps : ℕ → Measure (DPath T₃ S × D0 T₁ T₂))
    (hps : ∀ n, IsProbabilityMeasure (ps n))
    (hxcompact : RelCompactLaws (fun n => Measure.map
      (fun p => restrictToRange h₂₃ y (p.1 : DPath T₃ S)) (ps n)))
    (hyconv : Weakly (fun n => Measure.map (fun p => p.2.1) (ps n)) (Measure.dirac y.1))
    (hfdd : ∃ A : Set T₁, Dense A ∧ ∀ (k : ℕ) (ts : Fin k → T₁),
      (∀ i, ts i ∈ A) → ∃ q : Measure (Fin k → S),
        Weakly (fun n => Measure.map (composeEval h₂₃ ts) (ps n)) q) :
    (∀ (p : DPath T₃ S × D0 T₁ T₂) (t : T₁),
      (composeD h₂₃ p).1 t = p.1.1 ⟨p.2.1.1 t, h₂₃ (p.2.2.2 t)⟩) ∧
    (∀ (z : DPath T₁ S) (u : timeRange y),
      (inverseD y z).1 u = z.1 (Classical.choose u.2)) ∧
    ∃ q : Measure (DPath T₁ S),
      Weakly (fun n => Measure.map (composeD h₂₃) (ps n)) q ∧
      Weakly (fun n => Measure.map (fun p => restrictToRange h₂₃ y p.1) (ps n))
        (Measure.map (inverseD y) q) := by sorry

end WhittFLT.TimeReversal.Supplement
