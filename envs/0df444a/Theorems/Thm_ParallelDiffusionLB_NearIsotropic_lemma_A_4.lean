-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_4
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:41.8817+00:00
-- url     : https://prove2.me/theorems/4a84efc1-682d-46c1-bf7f-af667d839e1f
-- title:
--   Lemma A.4 — Information-density concentration and nearby noise
-- statement:
--   For $m\ge1$ and $\tau>0$, the law under standard Gaussian $Z$ of $\ell_\tau(y,y+\tau Z)$ is the same for every $y\in V_m$, and its expectation is $m\alpha_\tau$. For either sign and every $t\ge0$,
--   $$\Pr_Z[\pm(\ell_\tau(y,y+\tau Z)-m\alpha_\tau)\ge t]\le \exp(-\tau^2t^2/(8m)).$$
--   For every $0<u\le v$,
--   $$0\le\alpha_u-\alpha_v\le\log(v/u).$$
--   Both the law and mean assertions, both tails, and the nearby-noise bound are included.
--
--   Differences from the source:
--   - encoding: nonempty subsets of {−1,+1}^m → finite sets of Boolean-labelled cube vertices with nonemptiness or positive prescribed cardinality; reason: the vertex map is a bijection and the uniform subset law samples without replacement
--   - encoding: either sign in (23) → a real sign constrained to equal +1 or −1; reason: this includes exactly the two tails
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.4, p. 21

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

theorem lemma_A_4 (m : ℕ) (hm : 1 ≤ m) :
    (∀ τ : ℝ, 0 < τ →
      (∀ y y' : Cube m,
        (stdGaussian (E m)).map (fun z => logLikelihood τ y (vertex y + τ • z)) =
        (stdGaussian (E m)).map (fun z => logLikelihood τ y' (vertex y' + τ • z))) ∧
      (∀ y : Cube m,
        (∫ z, logLikelihood τ y (vertex y + τ • z) ∂(stdGaussian (E m))) =
          m * informationLevel m τ) ∧
      (∀ y : Cube m, ∀ sign : ℝ, (sign = 1 ∨ sign = -1) → ∀ t : ℝ, 0 ≤ t →
        (stdGaussian (E m)).real {z | t ≤
          sign * (logLikelihood τ y (vertex y + τ • z) - m * informationLevel m τ)} ≤
          Real.exp (-(τ ^ 2 * t ^ 2) / (8 * m)))) ∧
    (∀ u v : ℝ, 0 < u → u ≤ v →
      0 ≤ informationLevel m u - informationLevel m v ∧
      informationLevel m u - informationLevel m v ≤ Real.log (v / u)) := by sorry

end ParallelDiffusionLB.NearIsotropic
