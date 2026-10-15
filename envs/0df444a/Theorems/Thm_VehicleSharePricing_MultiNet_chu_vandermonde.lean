-- Prove2me | Theorems.Thm_VehicleSharePricing_MultiNet_chu_vandermonde
-- name    : VehicleSharePricing.MultiNet.chu_vandermonde
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:20.487374+00:00
-- url     : https://prove2.me/theorems/4c9ab640-4b17-4123-a67c-eaf4c62ec5ca
-- title:
--   §6, proof of Theorem 4, p. 18 — Chu–Vandermonde: $\sum_{K_1=0}^{K}\binom{K+T-K_1-T_1-1}{K-K_1}\binom{T_1+K_1-1}{K_1}=\binom{K+T-1}{K}$
-- statement:
--   Let $T_1,T_2>0$ be real numbers, $T=T_1+T_2$, and $K\in\mathbb N$. With the binomial coefficient $\binom{x}{k}=\prod_{i=0}^{k-1}(x-i)/k!$ for real $x$,
--   $$\sum_{K_1=0}^{K}\binom{K+T-K_1-T_1-1}{K-K_1}\binom{T_1+K_1-1}{K_1}=\binom{K+T-1}{K}.$$
--
--   In the proof of Theorem 4 the paper takes $T_i=N_i+M_i$ (number of locations plus workload of network $i$). Dividing by the right-hand side turns the summands into probability weights on $K_1\in\{0,\dots,K\}$, which the paper uses to average the two-network objective.
--
--   **Formalization Note** The identity holds for all real $T_1,T_2$; the positivity hypotheses are those of the paper's application ($T_i=N_i+M_i\ge1$). It is an instance of the Vandermonde identity for generalized binomial coefficients (Mathlib's `Ring.add_choose_eq`), written with the page's binomial.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 18, §6, proof of Theorem 4 (Chu–Vandermonde identity)

import Mathlib
import Definitions.Def_VehicleSharePricing_MultiNet_GenBinom

namespace VehicleSharePricing.MultiNet

open Finset

/-- §6, proof of Theorem 4, p. 18 (Chu–Vandermonde identity), with `T = T₁ + T₂` and the
real-argument binomial `gbinom` of p. 18:
`∑_{K₁=0}^{K} C(K + T - K₁ - T₁ - 1, K - K₁) C(T₁ + K₁ - 1, K₁) = C(K + T - 1, K)`. -/
theorem chu_vandermonde (T₁ T₂ : ℝ) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (K : ℕ) :
    ∑ K₁ ∈ Finset.range (K + 1),
        gbinom ((K : ℝ) + (T₁ + T₂) - (K₁ : ℝ) - T₁ - 1) (K - K₁) * gbinom (T₁ + (K₁ : ℝ) - 1) K₁ =
      gbinom ((K : ℝ) + (T₁ + T₂) - 1) K := by sorry

end VehicleSharePricing.MultiNet
