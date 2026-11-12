-- Prove2me | Theorems.Thm_PersuasionByParts_Known_pooling_semantics
-- name    : PersuasionByParts.Known.pooling_semantics
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:21.608597+00:00
-- url     : https://prove2.me/theorems/ba36fea1-049e-451c-9f3f-67a0ae2380ba
-- title:
--   §1.1 — Fractional top-pool normalization and mean identity
-- statement:
--   Let $\mu$ be any Borel probability law on $\mathbb R$ with finite absolute mean, and let $s\in[0,1]$. Let $w_s$ be the atom-aware top-mass selector, $m_\mu$ its upper-quantile mean, and $K_s$ its pool/reveal Markov kernel. Then
--
--   $$0\le w_s(z)\le1\quad\text{for every }z,\qquad \int w_s\,d\mu=s,\qquad \int z w_s(z)\,d\mu=s\,m_\mu(s).$$
--
--   The probability of the pool tag under $K_s$ is $s$. When $s>0$, the posterior mean at this tag equals $m_\mu(s)$. There is no assertion of a conditional mean on a zero-probability pool.
--
--   These are the normalization and conditional-mean meanings of the unnumbered top-pool definition on printed page 3. This supporting statement connects the quantile formula to the actual randomized experiment, including atomic laws and the endpoints.
--
--   Differences from the source:
--   - encoding: fractional-atom top-s pools and their quantile means for 0 < s ≤ 1 → the published upper quantile integral divided by s, the exact boundary-atom fraction, explicit zero/all selectors, and independent uniform randomization into Unit ⊕ ℝ pool/reveal tags; reason: interior quantiles are finite for arbitrary real probability laws; endpoint quantile values affect only a null set in the integral, and a zero-mass pool is never treated as a positive-mass conditional mean
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed p. 3 / PDF p. 4, §1.1 unnumbered top-mass selector and displayed pool-mean identity

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Pooling

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known

/-- Section 1.1, unnumbered top-pool definition and mean identity, printed p. 3.
The mean at a zero-mass pool is never asserted to be a conditional mean. -/
theorem pooling_semantics (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (s : ℝ) (hs : s ∈ Icc 0 1) :
    (∀ z : ℝ, topSelector μ s z ∈ Icc 0 1) ∧
    (∫ z, topSelector μ s z ∂μ) = s ∧
    (∫ z, topSelector μ s z * z ∂μ) = s * poolMean μ s ∧
    (poolKernel μ s ∘ₘ μ).real {Sum.inl ()} = s ∧
    (0 < s → PersuasionNetworks.posteriorMean μ (poolKernel μ s) (Sum.inl ()) =
      poolMean μ s) := by sorry

end PersuasionByParts.Known
