-- Prove2me | Theorems.Thm_UnivAccel_discrete_ms_rate
-- name    : UnivAccel.discrete_ms_rate
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:18:09.595231+00:00
-- url     : https://prove2.me/theorems/df5c1208-00ca-47b0-8e20-7f8377ea8902
-- title:
--   §4.2 — discrete MS rate $H_N \le H_0\exp[-\min\{N,\sqrt\mu rN^{3/2}/\sqrt{H_0}\}/(8\sqrt2)]$ and (21)
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Let $\mu > 0$, $r > 0$, and let $H_0, \dots, H_N$ and $h_1, \dots, h_N$ be real numbers with $H_0 > 0$, $H_i \ge 0$, $h_i > 0$, satisfying the per-step loss (18) at every step:
--   $$
--   H_{i-1} - H_i \ge h_i\sqrt\mu\, H_i + \frac{r^2(1 + 2h_i\sqrt\mu)^2}{4h_i^2}, \qquad i = 1, \dots, N .
--   $$
--   Then
--   $$
--   H_N \le H_0 \exp\Big[-\frac{1}{8\sqrt2}\min\Big\{N, \frac{\sqrt\mu\, r}{\sqrt{H_0}} N^{3/2}\Big\}\Big],
--   $$
--   and halving the potential requires $N = O(1 + (H_0/(\mu r^2))^{1/3})$ steps (21): $H_N \le H_0/2$ whenever $N \ge C(1 + (H_0/(\mu r^2))^{1/3})$.
--
--   With $H_0 = O(\mu R^2)$ this is the Monteiro–Svaiter bound $O(1 + (R/r)^{2/3})$ for the implicit Euler method.
--
--   Differences from the source:
--   - generalization: H_i the potentials and h_i the durations of the implicit Euler method → any real sequences with H_0 > 0, H_i ≥ 0, h_i > 0 satisfying (18) at every step; reason: the derivation on p.13 uses only these properties; the method's potentials are one such sequence
--   - reading: halving H requires N = O(1 + (H0/(μr²))^{1/3}) steps (21) → ∃ C > 0, quantified first, with H_N ≤ H_0/2 whenever N ≥ C(1 + (H0/(μr²))^{1/3}); reason: O(·) as an absolute constant; "requires" is the number of steps that suffices
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §4.2 "From the per-step loss to the discrete MS rate", eqs. (19)–(21), p.13

import Mathlib

namespace UnivAccel

/-- §4.2 "From the per-step loss to the discrete MS rate", (19)–(21), p.13 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)). Let
`μ > 0`, `r > 0`, and let `H_0, …, H_N` be potentials and `h_1, …, h_N > 0` step durations with
`H_0 > 0`, `H_i ≥ 0`, and, for `i = 1, …, N`, the per-step loss (18),
`H_{i−1} − H_i ≥ h_i√μ H_i + r²(1 + 2h_i√μ)²/(4h_i²)`. Then
`H_N ≤ H_0 exp[−(1/(8√2)) min{N, (√μ r/√H_0) N^{3/2}}]`; in particular halving `H` requires
`N = O(1 + (H_0/(μr²))^{1/3})` steps (21): there is an absolute constant `C` such that
`H_N ≤ H_0/2` whenever `N ≥ C(1 + (H_0/(μr²))^{1/3})`.

**Formalization Note** Stated for arbitrary real sequences satisfying (18) at every step; the
potentials of the method are one such sequence. `O(·)` is an absolute `C > 0` quantified first. -/
theorem discrete_ms_rate :
    ∃ C : ℝ, 0 < C ∧
    ∀ (μ r : ℝ) (h H : ℕ → ℝ) (N : ℕ), 0 < μ → 0 < r → 0 < H 0 →
      (∀ i, 1 ≤ i → i ≤ N → 0 < h i) → (∀ i, i ≤ N → 0 ≤ H i) →
      (∀ i, 1 ≤ i → i ≤ N →
        H (i - 1) - H i ≥ h i * Real.sqrt μ * H i
          + r ^ 2 * (1 + 2 * h i * Real.sqrt μ) ^ 2 / (4 * h i ^ 2)) →
      H N ≤ H 0 * Real.exp (-(1 / (8 * Real.sqrt 2)) *
          min (N : ℝ) (Real.sqrt μ * r / Real.sqrt (H 0) * (N : ℝ) ^ ((3 : ℝ) / 2))) ∧
      (C * (1 + (H 0 / (μ * r ^ 2)) ^ ((1 : ℝ) / 3)) ≤ (N : ℝ) → H N ≤ H 0 / 2) := by sorry

end UnivAccel
