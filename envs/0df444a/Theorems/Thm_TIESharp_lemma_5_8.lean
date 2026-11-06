-- Prove2me | Theorems.Thm_TIESharp_lemma_5_8
-- name    : TIESharp.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:13.994197+00:00
-- url     : https://prove2.me/theorems/dd921394-b49a-4348-9a54-8aa3958ad682
-- title:
--   Lemma 5.8 — scalar improvement: inequality (5.6)
-- statement:
--   For every probability vector $\theta$ on seven machines with $3/4\le\|\theta\|_2\le1$, every machine $i$ with $\theta_i=\max_k\theta_k$, and every $1\le d_i\le2$,
--   $$(2-d_i)\theta_i(1-\theta_i)+\frac{\big((d_i+1)\theta_i-\|\theta\|_2-1\big)_+^2}{4\big((d_i^2+1)\|\theta\|_2+1-(d_i+1)\theta_i\big)}\ \ge\ 2(1-\|\theta\|_2)(\|\theta\|_2-3/4).\tag{5.6}$$
--   With Lemmas 5.6 and 5.7 this removes the excess $1/32$ of the general bound at $n=7$.
--
--   Differences from the source: none.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 5.8, p.28, (5.6)

import Mathlib

set_option autoImplicit false

namespace TIESharp

/-- **Lemma 5.8 (Scalar improvement)** (Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*,
arXiv:2611.05134, Lemma 5.8, p.28). Inequality (5.6),
`(2 − d_i) θ_i (1 − θ_i) + ((d_i + 1)θ_i − ‖θ‖₂ − 1)₊² / (4((d_i² + 1)‖θ‖₂ + 1 − (d_i + 1)θ_i))
  ≥ 2(1 − ‖θ‖₂)(‖θ‖₂ − 3/4)`,
holds for every probability vector `θ` with `3/4 ≤ ‖θ‖₂ ≤ 1`, every machine `i` with
`θ_i = max_k θ_k`, and every `1 ≤ d_i ≤ 2`.

**Formalization Note.** `θ` is a probability vector on the seven machines of §5.7;
`‖θ‖₂ = √(Σ_ℓ θ_ℓ²)` and `(x)₊ = max x 0`. -/
theorem lemma_5_8 (θ : Fin 7 → ℝ) (hθnn : ∀ l, 0 ≤ θ l) (hθsum : ∑ l, θ l = 1)
    (hθ₁ : 3 / 4 ≤ Real.sqrt (∑ l, θ l ^ 2)) (hθ₂ : Real.sqrt (∑ l, θ l ^ 2) ≤ 1)
    (i : Fin 7) (hi : ∀ l, θ l ≤ θ i) (d : ℝ) (hd₁ : 1 ≤ d) (hd₂ : d ≤ 2) :
    (2 - d) * θ i * (1 - θ i)
      + (max ((d + 1) * θ i - Real.sqrt (∑ l, θ l ^ 2) - 1) 0) ^ 2
        / (4 * ((d ^ 2 + 1) * Real.sqrt (∑ l, θ l ^ 2) + 1 - (d + 1) * θ i))
      ≥ 2 * (1 - Real.sqrt (∑ l, θ l ^ 2)) * (Real.sqrt (∑ l, θ l ^ 2) - 3 / 4) := by sorry

end TIESharp
