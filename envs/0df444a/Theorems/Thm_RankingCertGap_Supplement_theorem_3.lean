-- Prove2me | Theorems.Thm_RankingCertGap_Supplement_theorem_3
-- name    : RankingCertGap.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:57:08.164208+00:00
-- url     : https://prove2.me/theorems/519f1460-3005-4aac-98c4-09a06ca040de
-- title:
--   Theorem 3 — exact unrestricted-degree capacity, competitiveness, gap, and optimizer
-- statement:
--   Let $\mathcal F$ be the nondecreasing, right-continuous admissible gain-sharing profiles. For every $f\in\mathcal F$, the unrestricted finite-instance certifying value is
--   $$
--   \chi(f;\infty)=\min_{t\in[0,1]}H_f(t).
--   $$
--   Moreover,
--   $$
--   \Gamma(\infty)=\gamma(\infty)=1-\frac1e,\qquad \Delta(\infty)=0.
--   $$
--   The unique optimizer is $f^\star_\infty(t)=e^{t-1}$ on $[0,1]$.
--
--   This identifies both the exact inner value for every admissible monotone profile and the unique profile attaining the classical unrestricted RANKING guarantee.
--
--   **Formalization Note** The minimum is stated by exhibiting an attaining point and comparing it with every other point of $[0,1]$. Optimizer uniqueness is pointwise on the paper's domain $[0,1]$.
--
--   Differences from the source:
--   - encoding: $f:[0,1]\to[0,1]$ and $f^\star_\infty(t)=e^{t-1}$ → total real functions whose values on $[0,1]$ are unchanged; reason: the published profile class uses total functions and scores only read the source interval
--   - encoding: $\min_{t\in[0,1]}H_f(t)$ → an attaining $t\in[0,1]$ whose value is no larger than every other value; reason: this is the literal minimum and avoids a junk real infimum
--   - encoding: unique optimizer as a function on $[0,1]$ → equality at every point of $[0,1]$; reason: total-function extensions outside the source domain are irrelevant
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Theorem 3, p.8, eqs. (14)–(15)

import Mathlib
import Definitions.Def_RankingCertGap_Supplement_Objects

set_option autoImplicit false

namespace RankingCertGap.Supplement

/-- **Theorem 3 (Unrestricted online degree).** Xu, *Certifying Capacity and Gaps of the
Rank-Dependent Gain-Sharing Framework for Ranking*, arXiv:2610.17545 (held file sha256 75896dd9…),
Theorem 3, p.8, eqs. (14)–(15). For every `f ∈ 𝒽`, the inner value is the attained minimum of
`H_f` on `[0,1]`; the capacity and competitiveness are `1 - 1/e`, the gap is zero, and the
exponential profile is the unique optimizer.

**Formalization Note.** `unrestricted` is the class of all finite instances, not an
infinity-regular class. The attained minimum is written with its minimizer, avoiding any real
`sInf` convention. Optimizer equality is pointwise on `[0,1]`, the source domain; total-function
extensions outside that interval are immaterial. -/
theorem theorem_3 :
    (∀ f : ℝ → ℝ, f ∈ classF →
      ∃ t ∈ Set.Icc (0 : ℝ) 1,
        chiC f unrestricted = Hf f t ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1, Hf f t ≤ Hf f u) ∧
    GammaC classF unrestricted = 1 - 1 / Real.exp 1 ∧
    gammaC unrestricted = 1 - 1 / Real.exp 1 ∧
    gapC classF unrestricted = 0 ∧
    expProfile ∈ classF ∧
    chiC expProfile unrestricted = GammaC classF unrestricted ∧
    (∀ f : ℝ → ℝ, f ∈ classF →
      chiC f unrestricted = GammaC classF unrestricted →
      ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = expProfile y) := by sorry

end RankingCertGap.Supplement
