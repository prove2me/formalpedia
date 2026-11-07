-- Prove2me | Theorems.Thm_QubitFreqSensing_section_6_eq_18
-- name    : QubitFreqSensing.section_6_eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:29.489839+00:00
-- url     : https://prove2.me/theorems/9b08acde-cbb5-4513-82bc-e152b4b39c9f
-- title:
--   §6, eq. (18) — a uniform random wait gives detection probability $\ge1/(8\pi)$ for every phase
-- statement:
--   Let $N\ge1$, $\omega_1,\dots,\omega_N>0$, $\gamma>0$, $B>0$ and $T\ge\sqrt N/(\gamma B)$, and let $D=2\pi/\omega_{\min}$ with $\omega_{\min}=\min_i\omega_i$. Let $f_0,f_1$ be integrable on $[0,T]$ and satisfy (16): for each $i$ some $b$ has $\bigl|\int_0^Tf_b(t)\cos(\omega_it)\,dt\bigr|\ge\gamma T/\sqrt N$. Then for every $i$ and every phase $\phi\in\mathbb R$,
--
--   $$
--   \mathbb E_{b,\tau}\bigl[\sin^2 A_{\omega_i,\phi,T,\tau}(f_b)\bigr]=\frac12\sum_{b\in\{0,1\}}\frac1D\int_0^D\sin^2\Bigl(B\int_0^Tf_b(t)\cos\bigl(\omega_i(t+\tau)+\phi\bigr)\,dt\Bigr)\,d\tau\ \ge\ \frac1{8\pi}. \tag{18}
--   $$
--
--   Here $b$ is uniform on $\{0,1\}$ and $\tau$ is uniform on $[0,D]$, independent of $b$. By §7, $\sin^2 A_{\omega_i,\phi,T,\tau}(f_b)$ is the probability that a trial of Protocol 1 returns $1$, so (18) is the per-trial detection bound of the protocol.
--
--   Differences from the source:
--   - generalization: f0, f1 : [0, T] → {−1, 1} piecewise constant, from Theorem 5.13 → f_0, f_1 any real functions integrable on [0, T] satisfying (16); reason: the argument of §6 uses only (16) and integrability; the ±1 patterns are a special case
--   - encoding: E_{b,τ} with b ∼ Unif{0, 1}, τ ∼ Unif[0, D] → ½ Σ_b (1/D)∫_0^D; reason: explicit average
--   - generalization: γ the universal constant of Theorem 5.13 → any γ > 0 for which f_0, f_1 satisfy (16), with T ≥ √N/(γB); reason: the argument of §6 uses only (16) and B γT/√N ≥ 1; Theorem 5.13's γ is a special case
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), §6, pp.23–24, display (18) (PDF pp.23–24)

import Mathlib
import Definitions.Def_QubitFreqSensing_SignPattern

open Real

namespace QubitFreqSensing

/-- **§6, display (18)** (random wait handles the unknown phase; Chen, Coladangelo, Li, Zhang,
manuscript (STOC 2027 submission), §6, pp.23–24, eq. (18)). Let `f₀, f₁` satisfy (16): for each
`i` some `b` has `|∫₀^T f_b(t) cos(ω_i t) dt| ≥ γT/√N`. With `B > 0`, `T ≥ √N/(γB)`,
`D = 2π/ω_min`, and `P_{i,b}(T, τ) = sin²(A_{ω_i,ϕ,T,τ}(f_b))`: "Finally, the protocol chooses b
uniformly from {0, 1}, independently of τ. For each candidate frequency, at least one of the two
functions f0, f1 satisfies the required bound. So, the probability of selecting such a function is
at least 1/2. Thus, for every candidate frequency and every phase, E_{b,τ}[Pi,b(T, τ)] ≥
(1/2) · (1/(4π)) = 1/(8π). (18)"

**Formalization Note** `E_{b,τ}` is the average over `b ∈ {0, 1}` (weight `1/2` each) and
`τ ∼ Unif[0, D]`. The proof uses only (16) and integrability, so `f_b` are arbitrary
interval-integrable real functions; the `±1` patterns of Theorem 5.13 are a special case.
`ω_min = ⨅ i, ω i`. -/
theorem section_6_eq_18 (N : ℕ) (hN : 1 ≤ N) (ω : Fin N → ℝ) (hω : ∀ i, 0 < ω i)
    (γ B T : ℝ) (hγ : 0 < γ) (hB : 0 < B) (hT : Real.sqrt N / (γ * B) ≤ T)
    (f : Fin 2 → ℝ → ℝ) (hf : ∀ b, IntervalIntegrable (f b) MeasureTheory.volume 0 T)
    (h16 : ∀ i, ∃ b, γ * T / Real.sqrt N ≤ |∫ t in (0 : ℝ)..T, f b t * Real.cos (ω i * t)|) :
    ∀ i, ∀ ϕ : ℝ,
      1 / (8 * π) ≤ (1 / 2) * ∑ b : Fin 2, (1 / (2 * π / ⨅ k, ω k)) *
        ∫ τ in (0 : ℝ)..(2 * π / ⨅ k, ω k), Real.sin (corrA B (ω i) ϕ T τ (f b)) ^ 2 := by sorry

end QubitFreqSensing
