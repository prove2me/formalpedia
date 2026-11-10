-- Prove2me | Theorems.Thm_RandOrderKnapGAP_Integral_lemma_A_2
-- name    : RandOrderKnapGAP.Integral.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:26:07.328803+00:00
-- url     : https://prove2.me/theorems/07f61a1e-ae74-4eb0-a425-953370c15064
-- title:
--   Lemma A.2 — a load stochastically below a target can be padded up to the target law with fresh randomness
-- statement:
--   Let $W,Y\in[0,1]$ be random variables with laws $\rho$ and $\nu$ such that
--   $$\Pr(W>z)\le\Pr(Y>z)\qquad\text{for every }z\in[0,1].$$
--   Then, using $W$, the two distributions and fresh randomness, one can construct $Z$ with $Z\ge W$ and $Z\sim Y$. Precisely: there is a measurable map $f$, determined by $\rho$ and $\nu$, such that if $U$ is uniform on $[0,1]$ and independent of $W$, then $Z=f(W,U)$ satisfies $Z\ge W$ and has law $\nu$.
--
--   This is the padding step of the algorithm: after a decision the virtual load has no more mass above any threshold than the next target distribution, and padding raises it to exactly that distribution without ever lowering it.
--
--   Differences from the source:
--   - encoding: random variables W, Y ∈ [0, 1]; Z constructed from W, the two distributions and fresh randomness → laws ρ, ν on [0, 1]; ∃ measurable f : ℝ × ℝ → ℝ (chosen after ρ, ν) with w ≤ f(w, u) for all (w, u) and the law of f under ρ ⊗ Uniform[0,1] equal to ν; reason: on any probability space carrying W ∼ ρ and an independent uniform U this is the paper's Z = f(W, U); f depends only on the two laws
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), p. 24 (PDF 26), Lemma A.2 (= Lemma 3.2)

import Mathlib

open MeasureTheory

namespace RandOrderKnapGAP.Integral

/-- **Lemma A.2** (increasing a load to a prescribed distribution), p. 24. Let `ρ` (the law of
`W`) and `ν` (the law of `Y`) be probability distributions on `[0, 1]` with
`Pr(W > z) ≤ Pr(Y > z)` for every `z ∈ [0, 1]`. Then there is a measurable map `f`, built from
`ρ` and `ν` only, such that for `W ∼ ρ` and an independent uniform `U` on `[0, 1]` (fresh
randomness), `Z = f(W, U)` satisfies `Z ≥ W` (on every outcome) and `Z ∼ ν`. -/
theorem lemma_A_2 (ρ ν : Measure ℝ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (hρ : ρ (Set.Icc 0 1) = 1) (hν : ν (Set.Icc 0 1) = 1)
    (hdom : ∀ z ∈ Set.Icc (0 : ℝ) 1, ρ (Set.Ioi z) ≤ ν (Set.Ioi z)) :
    ∃ f : ℝ × ℝ → ℝ, Measurable f ∧ (∀ x : ℝ × ℝ, x.1 ≤ f x) ∧
      (ρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map f = ν := by sorry

end RandOrderKnapGAP.Integral
