-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_lemma_2_1
-- name    : PDynTreeEmbed.Main.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:31:52.55041+00:00
-- url     : https://prove2.me/theorems/ce7623e8-0179-4fbc-af84-452c2acbecc1
-- title:
--   Lemma 2.1 — with exponential shifts, the minimizer changes at most H_n times in expectation
-- statement:
--   Let $T\ge1$ and let $\alpha^{(1)},\dots,\alpha^{(T)}\in\mathbb R^n$ be a predetermined sequence of vectors with $\alpha^{(t)}_i\ge0$ for all $t\in[T]$, $i\in[n]$, such that in each step exactly one coordinate increases: for every $t\in[T-1]$ there is $i$ with $\alpha^{(t)}_i<\alpha^{(t+1)}_i$ and $\alpha^{(t)}_j=\alpha^{(t+1)}_j$ for $j\ne i$. Draw independent $R_i\sim\mathrm{Exp}(\lambda)$, $\lambda>0$, put $\beta^{(t)}_i=\alpha^{(t)}_i-R_i$, $\beta^{(t)}_0=0$ and $I^{(t)}=\arg\min_{0\le i\le n}\beta^{(t)}_i$. Then
--   $$\mathbb E\Big[\sum_{t\in[T-1]}\mathbf 1\{I^{(t+1)}\ne I^{(t)}\}\Big]\le H_n.$$
--   This is the stability of exponential shifts behind every recourse bound of the paper.
--
--   Differences from the source:
--
--   - encoding: I^(t) = arg min (an index; ties have probability zero) → the argmin set argminSet; a change is a change of the set; reason: ties have probability zero, so the two counts agree almost surely
--   - encoding: vectors α^(t) for t ∈ [T], the dummy β_0 = 0 → α : ℕ → Fin n → ℝ constrained on t ∈ [1, T]; β^(t) = Fin.cons 0 (α t − R) : Fin (n+1) → ℝ; reason: values outside [T] are never used; index 0 is the dummy
--   - encoding: R_i ∼ Exp(λ) independent; E[·] → random variables R i on any probability space with iIndepFun and law expMeasure λ (rate λ); the expectation is the lintegral of the count; reason: the statement about every realization of the law
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 6, Lemma 2.1

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Improving
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Lemma 2.1** (p. 6). Let `α^(1), …, α^(T)` be a predetermined sequence of nonnegative vectors in
`ℝⁿ` such that between consecutive times exactly one coordinate strictly increases and the others
stay equal. Let `R_1, …, R_n` be independent `Exp(λ)` random variables (`λ > 0`), and put
`β^(t)_i = α^(t)_i − R_i`, `β^(t)_0 = 0`. Then the expected number of times `t ∈ [T − 1]` at which
the argmin set of `(β^(t)_0, …, β^(t)_n)` changes is at most the harmonic number `H_n`. -/
theorem lemma_2_1 (n T : ℕ) (α : ℕ → Fin n → ℝ)
    (hnonneg : ∀ t ∈ Finset.Icc 1 T, ∀ i, 0 ≤ α t i)
    (hstep : ∀ t ∈ Finset.Ico 1 T,
      ∃ i, α t i < α (t + 1) i ∧ ∀ j, j ≠ i → α t j = α (t + 1) j)
    (lam : ℝ) (hlam : 0 < lam) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R : Fin n → Ω → ℝ) (hind : iIndepFun R P)
    (hlaw : ∀ i, P.map (R i) = expMeasure lam) :
    ∫⁻ ω, ∑ t ∈ Finset.Ico 1 T,
        (if argminSet (Fin.cons (0 : ℝ) (fun i => α (t + 1) i - R i ω) : Fin (n + 1) → ℝ) ≠
            argminSet (Fin.cons (0 : ℝ) (fun i => α t i - R i ω) : Fin (n + 1) → ℝ)
          then (1 : ℝ≥0∞) else 0) ∂P ≤
      ENNReal.ofReal (harmonic n : ℝ) := by sorry

end PDynTreeEmbed.Main
