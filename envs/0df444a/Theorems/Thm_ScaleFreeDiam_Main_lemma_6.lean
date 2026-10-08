-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_lemma_6
-- name    : ScaleFreeDiam.Main.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:08:36.967973+00:00
-- url     : https://prove2.me/theorems/51e443f8-b989-4f37-aeaf-af7b26e226bc
-- title:
--   Lemma 6, p. 15 — Chernoff–Janson tails for a sum of independent Bernoulli variables
-- statement:
--   Let $X=X_1+\dots+X_k$, where the $X_i$ are independent Bernoulli random variables with $\mathbb P(X_i=1)=p_i$, and let $\mu=\mathbb E X=p_1+\dots+p_k$. Then for every $t\ge0$,
--   $$
--   \mathbb P(X\ge\mu+t)\le\exp\Big(-\frac{t^2}{2(\mu+t/3)}\Big)
--   \qquad\text{and}\qquad
--   \mathbb P(X\le\mu-t)\le\exp\Big(-\frac{t^2}{2\mu}\Big).
--   $$
--   This is the probabilistic workhorse of §§6–8 of the paper (used in the proofs of Lemmas 7 and 11).
--
--   **Formalization Note** The $X_i$ are measurable real functions on a probability space, mutually independent, and almost surely $\{0,1\}$-valued. When $\mu=0$ Lean's division by zero gives $\exp(0)=1$ on the right, which is a true (trivial) bound.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 15, Lemma 6 (Janson)

import Mathlib

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : Fin k → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hX : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (p : Fin k → ℝ) (hp : ∀ i, P.real {ω | X i ω = 1} = p i) (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | (∑ i, p i) + t ≤ ∑ i, X i ω} ≤
        Real.exp (-(t ^ 2 / (2 * ((∑ i, p i) + t / 3)))) ∧
      P.real {ω | ∑ i, X i ω ≤ (∑ i, p i) - t} ≤
        Real.exp (-(t ^ 2 / (2 * (∑ i, p i)))) := by sorry

end ScaleFreeDiam.Main
