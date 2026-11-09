-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_3
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:59.622317+00:00
-- url     : https://prove2.me/theorems/60e30a21-03aa-415a-bb0a-a9547b061eff
-- title:
--   Lemma A.3 — Posterior score bounds
-- statement:
--   Let $m\ge1$, let $\nu$ be a probability measure supported on $[-1,1]^m$, and let $\tau>0$. Use the Gaussian posterior weighted by its likelihood at each $x$ to define its mean $M_\tau(x)$ and covariance $C_\tau(x)$. Then, everywhere,
--   $$s_{\nu,\tau}(x)=\frac{M_\tau(x)-x}{\tau^2},\qquad \nabla s_{\nu,\tau}(x)=-I_m/\tau^2+C_\tau(x)/\tau^4.$$
--   The score is globally Lipschitz with constant at most $\tau^{-2}+m\tau^{-4}$. For every nonempty $S\subseteq V_m$, every $x\in\mathbb R^m$, and every $y\in V_m$ in the last expression,
--   $$\|s_\tau^S(x)-s_\tau^0(x)\|\le2\sqrt m/\tau^2,\qquad \|\nabla_x\ell_\tau(y,x)\|\le2\sqrt m/\tau^2.$$
--   These are the specialized identities and all consequent bounds stated in the lemma.
--
--   Differences from the source:
--   - encoding: nonempty subsets of {−1,+1}^m → finite sets of Boolean-labelled cube vertices with nonemptiness or positive prescribed cardinality; reason: the vertex map is a bijection and the uniform subset law samples without replacement
--   - encoding: a supremum over query points of a norm or probability → the corresponding bound at every query point; reason: these bounds are equivalent and avoid real supremum defaults on unbounded sets
--   - encoding: conditional mean and covariance given Y+tau Z=x → Gaussian-likelihood-weighted posterior measure at every x; reason: the source explicitly specifies this everywhere version in §2.3
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.3, p. 21

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

/-- Posterior moments are the explicit Gaussian-weighted moments, so the identities hold everywhere. -/
theorem lemma_A_3 (m : ℕ) (hm : 1 ≤ m) (ν : Measure (E m)) [IsProbabilityMeasure ν]
    (hsupp : ν {y | ∀ i, |y i| ≤ 1} = 1) (τ : ℝ) (hτ : 0 < τ) :
    (∀ x, score ν τ x = (τ ^ 2)⁻¹ • (posteriorMean ν τ x - x)) ∧
    (∀ x, fderiv ℝ (score ν τ) x =
      -(τ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ (E m) +
        (τ ^ 4)⁻¹ • posteriorCov ν τ x) ∧
    (∀ x y, ‖score ν τ x - score ν τ y‖ ≤
      (1 / τ ^ 2 + m / τ ^ 4) * ‖x-y‖) ∧
    (∀ (S : Finset (Cube m)), S.Nonempty → ∀ x,
      ‖blockScore S τ x - nullScore m τ x‖ ≤ 2 * Real.sqrt m / τ ^ 2) ∧
    (∀ (y : Cube m) (x : E m),
      ‖gradient (logLikelihood τ y) x‖ ≤ 2 * Real.sqrt m / τ ^ 2) := by sorry

end ParallelDiffusionLB.NearIsotropic
