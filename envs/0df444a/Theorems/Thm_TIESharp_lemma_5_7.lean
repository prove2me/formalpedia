-- Prove2me | Theorems.Thm_TIESharp_lemma_5_7
-- name    : TIESharp.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:17.023194+00:00
-- url     : https://prove2.me/theorems/33199d31-48da-441b-b0d8-661ac292ca8e
-- title:
--   Lemma 5.7 — endpoint reduction to the scalar inequality (5.6)
-- statement:
--   Under the assumptions of Lemma 5.6, it suffices to prove, for every $1\le d_i\le2$,
--   $$(2-d_i)\theta_i(1-\theta_i)+\frac{\big((d_i+1)\theta_i-\|\theta\|_2-1\big)_+^2}{4\big((d_i^2+1)\|\theta\|_2+1-(d_i+1)\theta_i\big)}\ \ge\ 2(1-\|\theta\|_2)(\|\theta\|_2-3/4).\tag{5.6}$$
--   Formally: let $\theta$ be a probability vector on seven machines with $3/4<\|\theta\|_2<1$, $i$ a machine with $\theta_i=\max_\ell\theta_\ell$, $k\ne i$, and $d,s$ costs with $d\ge1$ and $d/2\le s\le1$. If (5.6) holds for every $d_i\in[1,2]$, then the saving subtracted in Lemma 5.6 covers the excess over four:
--   $$(2-d)\theta_i(1-\theta_i)+\frac{s\big(d\theta_i-s(\|\theta\|_2+\theta_k)\big)_+^2}{4\big((d^2+s^2)\|\theta\|_2-ds\theta_i+s^2\theta_k\big)}\ \ge\ 2(1-\|\theta\|_2)(\|\theta\|_2-3/4).$$
--
--   Differences from the source:
--   - reading: it suffices to prove (5.6) for every 1 ≤ d_i ≤ 2 → (5.6) on [1, 2] implies the Lemma 5.6 saving is at least 2(1 − ‖θ‖₂)(‖θ‖₂ − 3/4) on the cost region d ≥ 1, d/2 ≤ s ≤ 1, for k ≠ i; reason: this is the reduction the proof establishes and Proposition 5.5 uses
--   - generalization: the assumptions of Lemma 5.6 (θ from the mechanism, d_i > 1) → any probability vector θ on Fin 7 with 3/4 < ‖θ‖₂ < 1 and maximal θ_i; d ≥ 1; reason: the mechanism's θ and d_i > 1 are instances
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 5.7, p.28, (5.6)

import Mathlib

set_option autoImplicit false

namespace TIESharp

/-- **Lemma 5.7 (Endpoint reduction)** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Lemma 5.7, p.28). Under the assumptions of Lemma 5.6 it suffices to
prove, for every `1 ≤ d_i ≤ 2`,
`(2 − d_i) θ_i (1 − θ_i) + ((d_i + 1)θ_i − ‖θ‖₂ − 1)₊² / (4((d_i² + 1)‖θ‖₂ + 1 − (d_i + 1)θ_i))
  ≥ 2(1 − ‖θ‖₂)(‖θ‖₂ − 3/4)` (5.6).
Stated as an implication: for a probability vector `θ` on seven machines with
`3/4 < ‖θ‖₂ < 1`, a machine `i` with `θ_i = max_ℓ θ_ℓ`, a machine `k ≠ i`, and costs `d = d_i`,
`s = t_kj` in the region `d ≥ 1`, `d/2 ≤ s ≤ 1` of Lemma 5.6, if (5.6) holds for every
`d' ∈ [1, 2]`, then the saving subtracted in Lemma 5.6 covers the excess over four:
`(2 − d)θ_i(1 − θ_i) + s (dθ_i − s(‖θ‖₂ + θ_k))₊² / (4((d² + s²)‖θ‖₂ − d s θ_i + s² θ_k))
  ≥ 2(1 − ‖θ‖₂)(‖θ‖₂ − 3/4)`.

**Formalization Note.** `‖θ‖₂ = √(Σ_ℓ θ_ℓ²)` and `(x)₊ = max x 0`. The cost region `d ≥ 1`
contains Lemma 5.6's `d_i > 1`. -/
theorem lemma_5_7 (θ : Fin 7 → ℝ) (hθnn : ∀ l, 0 ≤ θ l) (hθsum : ∑ l, θ l = 1)
    (hθ₁ : 3 / 4 < Real.sqrt (∑ l, θ l ^ 2)) (hθ₂ : Real.sqrt (∑ l, θ l ^ 2) < 1)
    (i k : Fin 7) (hi : ∀ l, θ l ≤ θ i) (hki : k ≠ i)
    (d s : ℝ) (hd : 1 ≤ d) (hs₁ : d / 2 ≤ s) (hs₂ : s ≤ 1)
    (H : ∀ d' ∈ Set.Icc (1 : ℝ) 2,
      (2 - d') * θ i * (1 - θ i)
        + (max ((d' + 1) * θ i - Real.sqrt (∑ l, θ l ^ 2) - 1) 0) ^ 2
          / (4 * ((d' ^ 2 + 1) * Real.sqrt (∑ l, θ l ^ 2) + 1 - (d' + 1) * θ i))
        ≥ 2 * (1 - Real.sqrt (∑ l, θ l ^ 2)) * (Real.sqrt (∑ l, θ l ^ 2) - 3 / 4)) :
    (2 - d) * θ i * (1 - θ i)
      + s * (max (d * θ i - s * (Real.sqrt (∑ l, θ l ^ 2) + θ k)) 0) ^ 2
        / (4 * ((d ^ 2 + s ^ 2) * Real.sqrt (∑ l, θ l ^ 2) - d * s * θ i + s ^ 2 * θ k))
      ≥ 2 * (1 - Real.sqrt (∑ l, θ l ^ 2)) * (Real.sqrt (∑ l, θ l ^ 2) - 3 / 4) := by sorry

end TIESharp
