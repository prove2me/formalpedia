-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_6
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:40.624853+00:00
-- url     : https://prove2.me/theorems/9ae63972-26d7-46fb-b1bb-442d548d01eb
-- title:
--   Lemma A.6 — Without-replacement adaptation
-- statement:
--   Let $m\ge1$, $1\le n\le2^m$, and let $S$ be uniform among the $n$-element subsets of $V_m$. For every $\tau>0$ and $u\ge0$, with independent $Y\sim U_m$ and standard Gaussian $Z$,
--   $$E_S D_{KL}(p_\tau^S\|q_\tau)\le E_{Y,Z}\log\left(1+\frac{L_\tau(Y,Y+\tau Z)}n\right)\le e^{-u}+\log(1+2^m)\Pr[\ell_\tau(Y,Y+\tau Z)\ge\log n-u].$$
--   Both comparisons are included, with sampling without replacement. Expectations of nonnegative quantities are nonnegative Lebesgue integrals.
--
--   Differences from the source:
--   - encoding: nonempty subsets of {−1,+1}^m → finite sets of Boolean-labelled cube vertices with nonemptiness or positive prescribed cardinality; reason: the vertex map is a bijection and the uniform subset law samples without replacement
--   - encoding: nonnegative expectations and KL divergence → nonnegative Lebesgue integrals and Mathlib KL divergence valued in [0,∞]; reason: all values for the stated Gaussian mixtures are finite and the inequalities are unchanged; a divergent error cannot default to zero
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.6, p. 22

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

theorem lemma_A_6 (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ 2 ^ m)
    (τ u : ℝ) (hτ : 0 < τ) (hu : 0 ≤ u) :
    (∫⁻ S, InformationTheory.klDiv (blockLaw S τ) (nullLaw m τ) ∂(codebookLaw m n)) ≤
      (∫⁻ yz, ENNReal.ofReal (Real.log (1 + likelihood τ yz.1 (vertex yz.1 + τ • yz.2) / n))
        ∂((uniformFinset (Finset.univ : Finset (Cube m))).prod (stdGaussian (E m)))) ∧
    (∫⁻ yz, ENNReal.ofReal (Real.log (1 + likelihood τ yz.1 (vertex yz.1 + τ • yz.2) / n))
        ∂((uniformFinset (Finset.univ : Finset (Cube m))).prod (stdGaussian (E m)))) ≤
      ENNReal.ofReal (Real.exp (-u)) + ENNReal.ofReal (Real.log (1 + (2 : ℝ) ^ m)) *
        ((uniformFinset (Finset.univ : Finset (Cube m))).prod (stdGaussian (E m)))
          {yz | Real.log n - u ≤ logLikelihood τ yz.1 (vertex yz.1 + τ • yz.2)} := by sorry

end ParallelDiffusionLB.NearIsotropic
