-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_5
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:55.786443+00:00
-- url     : https://prove2.me/theorems/c7e6deef-2cb7-4d79-9b53-d8357a117cbf
-- title:
--   Lemma A.5 — KL–Fisher comparison
-- statement:
--   Let $\gamma>0$, $m\ge\max\{2,\sqrt2\gamma\}$, $S\subseteq V_m$ be nonempty, and $\tau\ge\gamma$. With $\tilde\tau=\tau\sqrt{1-\gamma^2/m^2}$, the null-score Fisher error satisfies
--   $$F_\tau(S)\le\frac{2em^2}{\gamma^2\tau^2}D_{KL}(p_{\tilde\tau}^S\|q_{\tilde\tau}).$$
--   The KL divergence and Fisher error retain extended nonnegative values. This is the specialized KL–Fisher comparison used by the dense-block estimate.
--
--   Differences from the source:
--   - encoding: nonempty subsets of {−1,+1}^m → finite sets of Boolean-labelled cube vertices with nonemptiness or positive prescribed cardinality; reason: the vertex map is a bijection and the uniform subset law samples without replacement
--   - encoding: nonnegative expectations and KL divergence → nonnegative Lebesgue integrals and Mathlib KL divergence valued in [0,∞]; reason: all values for the stated Gaussian mixtures are finite and the inequalities are unchanged; a divergent error cannot default to zero
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.5, p. 22

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

theorem lemma_A_5 (m : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hm : 2 ≤ m) (hmg : Real.sqrt 2 * γ ≤ m)
    (S : Finset (Cube m)) (hS : S.Nonempty) (τ : ℝ) (hτ : γ ≤ τ) :
    fisherError S τ ≤ ENNReal.ofReal (2 * Real.exp 1 * (m : ℝ) ^ 2 / (γ ^ 2 * τ ^ 2)) *
      InformationTheory.klDiv (blockLaw S (nearbyNoise m γ τ)) (nullLaw m (nearbyNoise m γ τ)) := by sorry

end ParallelDiffusionLB.NearIsotropic
