-- Prove2me | Theorems.Thm_PrettyGoodShadow_lemma_4_13
-- name    : PrettyGoodShadow.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:24:06.745123+00:00
-- url     : https://prove2.me/theorems/6beb2f35-3cdf-4ab8-af2e-e27646eab1b2
-- title:
--   Lemma 4.13 — $H(z_1,\dots,z_n)-H(z_1,\dots,z_m)\le(n-m)\mathbb E_\theta h(\theta)+\log\frac{n+1}{m+1}$
-- statement:
--   Let $\theta$ be any random variable on $[0,1]$ and let $1\le m\le n$. Let $z_1,\dots,z_n$ be conditionally independent $\mathrm{Ber}(\theta)$ given $\theta$. Then
--
--   $$
--   H(z_1,\dots,z_n)-H(z_1,\dots,z_m)\le(n-m)\,\mathbb E_\theta[h(\theta)]+\log\frac{n+1}{m+1},
--   $$
--
--   with $h$ the binary entropy. It bounds the classical entropy gap that appears in Lemma 4.10.
--
--   **Formalization Note** Entropies are in nats, and $h$ is Mathlib's `Real.binEntropy`. No finiteness of the law of $\theta$ is assumed.
--
--   Differences from the source:
--   - encoding: θ a random variable on [0,1]; z_i ∼ Ber(θ) → a probability measure μ on ℝ carried by [0,1]; the joint law E_θ ∏_i Ber(θ)(z_i); reason: the entropies depend only on these laws, and the page uses the z_i as conditionally independent given θ
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Lemma 4.13, p.27

import Mathlib
import Definitions.Def_PrettyGoodShadow_coinEntropy

open MeasureTheory

namespace PrettyGoodShadow

/-- **Lemma 4.13** (arXiv:2610.06781, sha256 bd055b7d…, p.27). Let `θ` be any random variable on `[0, 1]`, and let
`1 ≤ m ≤ n`. For `i ∈ [n]` let `z_i ∼ Ber(θ)`, conditionally independent given `θ`. Then
`H(z_1, …, z_n) − H(z_1, …, z_m) ≤ (n − m) · E_θ[h(θ)] + log((n + 1)/(m + 1))`.

**Formalization Note** `θ` is a probability measure `μ` on `ℝ` carried by `[0, 1]`, with no finiteness assumed.
`H` is Shannon entropy in nats and `h` is Mathlib's `Real.binEntropy`, also in nats. `Real.binEntropy` is
continuous and bounded on `[0, 1]`, so the integral is not a junk value. -/
theorem lemma_4_13 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ θ ∂μ, θ ∈ Set.Icc (0 : ℝ) 1)
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    coinEntropy μ n - coinEntropy μ m ≤
      ((n : ℝ) - m) * ∫ θ, Real.binEntropy θ ∂μ + Real.log (((n : ℝ) + 1) / ((m : ℝ) + 1)) := by sorry

end PrettyGoodShadow
