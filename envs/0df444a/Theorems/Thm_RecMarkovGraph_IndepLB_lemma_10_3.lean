-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_10_3
-- name    : RecMarkovGraph.IndepLB.lemma_10_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:40.808152+00:00
-- url     : https://prove2.me/theorems/6a51e70e-d154-4fa0-96ca-d09bf1f69c62
-- title:
--   Lemma 10.3, p. 28 — if Z_n → τ with Z_n > 0 and X_n/Z_n →p λ > 0, then X_n →p λτ
-- statement:
--   Let $(Z_n)$ be a sequence of positive reals converging to $\tau$, and let $X_1,X_2,\dots$ be random variables on one probability space such that $X_n/Z_n\to\lambda$ in probability for some constant $\lambda>0$. Then $X_n\to\lambda\tau$ in probability: for every $\varepsilon>0$,
--   $$\lim_{n\to\infty}\mathbb P\{|X_n-\lambda\tau|\le\varepsilon\}=1 .$$
--
--   This special case of Slutsky's theorem converts the concentration of $S_n/\mathbb E S_n$ into that of $S_n/\log n$.
--
--   Differences from the source:
--   - encoding: →p (convergence in probability, p. 4); random variables → ∀ ε > 0, Tendsto (fun n => P{|· − c| ≤ ε}) atTop (𝓝 1); Measurable (X n); λ is named lam; reason: the paper's own definition; λ is reserved in Lean
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 28, Lemma 10.3

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open MeasureTheory Filter Topology

theorem lemma_10_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (Z : ℕ → ℝ) (hZ : ∀ n, 0 < Z n)
    (τ : ℝ) (hZτ : Tendsto Z atTop (𝓝 τ)) (lam : ℝ) (hlam : 0 < lam)
    (hconv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P.real {ω | |X n ω / Z n - lam| ≤ ε}) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P.real {ω | |X n ω - lam * τ| ≤ ε}) atTop (𝓝 1) := by sorry

end RecMarkovGraph.IndepLB
