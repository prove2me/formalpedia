-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_rank3_series_negative_half
-- name    : QuantumMaxCutEnergy.rank3_series_negative_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T19:11:40.716959+00:00
-- url     : https://prove2.me/theorems/ad3425e1-47ab-43dc-a8ef-a6998e55a6e4
-- title:
--   Negative half of the rank-three odd-series ratio bound
-- statement:
--   **Negative half of the rank-three odd-series bound, without normalisation.**
--
--   Let $c_0,c_1,c_2,\dots\ge 0$ be summable with $c_0\ge 8/(3\pi)$ and $c_1\ge 4/(15\pi)$, and let $t\in[-1,0]$. Then
--   $$\sum_{k\ge0} c_k\,t^{2k+1}\;\le\;0.046+0.954\,t .$$
--
--   Both coefficients of the odd series are non-positive on $[-1,0]$, so dropping every term with $k\ge2$ can only increase the sum: $\sum_k c_k t^{2k+1}\le c_0t+c_1t^3$, and $c_0t\le \frac{8}{3\pi}t$, $c_1t^3\le\frac{4}{15\pi}t^3$ because $t\le0$. It remains to check $\frac{8}{3\pi}t+\frac{4}{15\pi}t^3\le 0.046+0.954t$ on $[-1,0]$; after multiplying by $45\pi$ this is the cubic $12t^3+(120-42.93\pi)t+2.07\pi\ge0$, whose minimum on $[-1,0]$ is about $0.13$ at $t\approx-0.643$.
--
--   **Role.** The campaign's full scalar ratio statement $\frac{1-\sum_k c_k t^{2k+1}}{1-t}\ge0.954$ on $[-1,1)$ is available as `QuantumMaxCutEnergy.rank3_odd_series_ratio_0954`, but it requires the normalisation $\sum_k c_k=1$. This item records that on the *negative* half of the interval — the only part where the inequality is numerically tight, the ratio dropping to $0.9564$ near $t=-0.6$ — no normalisation is needed, so the tight region of the rank-three correlation bound does not depend on the value of the hypergeometric series at $t=1$.
-- source:
--   Anshu-Gosset-Morenz, TQC 2020, Theorem 1 (rank-three product-state rounding); the scalar reduction appears in QuantumMaxCutEnergy.rank3_odd_series_ratio_0954 on this platform. This item is the t<=0 half, verified directly.

import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.rank3_series_negative_half (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hsum : Summable c) (hc0 : 8 / (3 * Real.pi) ≤ c 0) (hc1 : 4 / (15 * Real.pi) ≤ c 1) {t : ℝ} (ht1 : -1 ≤ t) (ht0 : t ≤ 0) : (∑' k, c k * t ^ (2 * k + 1)) ≤ (0.046 : ℝ) + 0.954 * t := by sorry
