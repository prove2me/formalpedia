-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_5
-- name    : RandOrderSort.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:03:17.281139+00:00
-- url     : https://prove2.me/theorems/2139fdcb-1e6d-42e5-afba-3f054f0ec1d4
-- title:
--   Lemma 4.5 — binomial and hypergeometric exponential moments
-- statement:
--   Let $Z\sim\mathrm{Bin}(\ell,p)$ with $\ell$ a nonnegative integer and $p\in[0,1]$, and write $\mu=\mathbb E[Z]=\ell p$. For every real $u$,
--   $$\mathbb E[e^{uZ}]\le(1-p+pe^u)^\ell\le\exp(\mu(e^u-1)).$$
--   If $\mu>0$, then
--   $$\mathbb P(Z\ge a)\le\exp\Bigl(-\frac{(a-\mu)^2}{2a}\Bigr)\quad(a\ge\mu),\qquad \mathbb P(Z\le a)\le\exp\Bigl(-\frac{(\mu-a)^2}{2\mu}\Bigr)\quad(0\le a\le\mu).$$
--   When $\mu=0$, $Z=0$ almost surely.
--
--   The same bounds hold for $Z\sim\mathrm{Hypergeom}(P,K,\ell)$: among $P\ge 1$ elements, $K$ are marked, and $Z$ counts the marked elements in a uniformly chosen $\ell$-subset, where $0\le K,\ell\le P$, $p=K/P$ and $\mu=\ell K/P$.
--
--   These are the tail bounds behind all probability estimates of §§4.2–4.4.
--
--   Differences from the source:
--   - encoding: Z ∼ Bin(ℓ, p) → sums against the mass function C(ℓ,z)p^z(1−p)^(ℓ−z), z = 0, …, ℓ; reason: the definition of the law
--   - encoding: Z ∼ Hypergeom(P, K, ℓ) → the uniform law on ℓ-subsets S of {0, …, P−1}, Z = |S ∩ Mk| with |Mk| = K; reason: the page's own description of the law
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.5, p.24, displays (26)–(28)

import Mathlib

namespace RandOrderSort

/-- **Lemma 4.5 (Binomial and hypergeometric exponential moments)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.24: "Binomial sampling.
Let Z ∼ Bin(ℓ, p), where ℓ is a nonnegative integer and p ∈ [0, 1], and write µ = E[Z] = ℓp. For every
u ∈ R, E[e^{uZ}] ≤ (1 − p + pe^u)^ℓ ≤ exp(µ(e^u − 1)). (26) If µ > 0, then
P(Z ≥ a) ≤ exp(−(a − µ)²/(2a)) (a ≥ µ), (27) P(Z ≤ a) ≤ exp(−(µ − a)²/(2µ)) (0 ≤ a ≤ µ). (28) When
µ = 0, Z = 0 almost surely. Sampling without replacement. The same bounds hold for
Z ∼ Hypergeom(P, K, ℓ): among P elements, K are marked, and Z counts the marked elements in a
uniformly chosen ℓ-subset. Here P ≥ 1 and 0 ≤ K, ℓ ≤ P are integers, p = K/P, and µ = E[Z] = ℓK/P."

**Formalization Note.** The binomial law is written through its mass function
`C(ℓ, z) p^z (1 − p)^{ℓ − z}`, `z = 0, …, ℓ`; the hypergeometric law is the uniform law of an
`ℓ`-subset `S` of `{0, …, P − 1}`, `Z = |S ∩ Mk|` for a marked set `Mk` of size `K`. "Z = 0 almost
surely" is `P(Z = 0) = 1`, resp. `Z(S) = 0` for every `ℓ`-subset. -/
theorem lemma_4_5 :
    (∀ (ℓ : ℕ) (p : ℝ), 0 ≤ p → p ≤ 1 →
      (∀ u : ℝ,
        ∑ z ∈ Finset.range (ℓ + 1), (ℓ.choose z : ℝ) * p ^ z * (1 - p) ^ (ℓ - z) * Real.exp (u * z) ≤
            (1 - p + p * Real.exp u) ^ ℓ ∧
          (1 - p + p * Real.exp u) ^ ℓ ≤ Real.exp (ℓ * p * (Real.exp u - 1))) ∧
      (0 < ℓ * p → ∀ a : ℝ, ℓ * p ≤ a →
        ∑ z ∈ (Finset.range (ℓ + 1)).filter (fun z : ℕ => a ≤ (z : ℝ)),
            (ℓ.choose z : ℝ) * p ^ z * (1 - p) ^ (ℓ - z) ≤
          Real.exp (-((a - ℓ * p) ^ 2 / (2 * a)))) ∧
      (0 < ℓ * p → ∀ a : ℝ, 0 ≤ a → a ≤ ℓ * p →
        ∑ z ∈ (Finset.range (ℓ + 1)).filter (fun z : ℕ => (z : ℝ) ≤ a),
            (ℓ.choose z : ℝ) * p ^ z * (1 - p) ^ (ℓ - z) ≤
          Real.exp (-((ℓ * p - a) ^ 2 / (2 * (ℓ * p))))) ∧
      (ℓ * p = 0 → (ℓ.choose 0 : ℝ) * p ^ 0 * (1 - p) ^ (ℓ - 0) = 1)) ∧
    (∀ (P K ℓ : ℕ) (Mk : Finset ℕ), 1 ≤ P → Mk ⊆ Finset.range P → Mk.card = K → ℓ ≤ P →
      (∀ u : ℝ,
        (∑ S ∈ (Finset.range P).powersetCard ℓ, Real.exp (u * (S ∩ Mk).card)) / (P.choose ℓ : ℝ) ≤
            (1 - (K : ℝ) / P + (K : ℝ) / P * Real.exp u) ^ ℓ ∧
          (1 - (K : ℝ) / P + (K : ℝ) / P * Real.exp u) ^ ℓ ≤
            Real.exp (ℓ * (K : ℝ) / P * (Real.exp u - 1))) ∧
      (0 < ℓ * (K : ℝ) / P → ∀ a : ℝ, ℓ * (K : ℝ) / P ≤ a →
        (((Finset.range P).powersetCard ℓ).filter (fun S => a ≤ ((S ∩ Mk).card : ℝ))).card /
            (P.choose ℓ : ℝ) ≤
          Real.exp (-((a - ℓ * (K : ℝ) / P) ^ 2 / (2 * a)))) ∧
      (0 < ℓ * (K : ℝ) / P → ∀ a : ℝ, 0 ≤ a → a ≤ ℓ * (K : ℝ) / P →
        (((Finset.range P).powersetCard ℓ).filter (fun S => ((S ∩ Mk).card : ℝ) ≤ a)).card /
            (P.choose ℓ : ℝ) ≤
          Real.exp (-((ℓ * (K : ℝ) / P - a) ^ 2 / (2 * (ℓ * (K : ℝ) / P))))) ∧
      (ℓ * (K : ℝ) / P = 0 → ∀ S ∈ (Finset.range P).powersetCard ℓ, (S ∩ Mk).card = 0)) := by sorry

end RandOrderSort
