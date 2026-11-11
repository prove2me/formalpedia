-- Prove2me | Theorems.Thm_SchattenSketch_Main_lemma_4_4
-- name    : SchattenSketch.Main.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:57:33.220224+00:00
-- url     : https://prove2.me/theorems/9d6b6637-e898-46b9-8a19-eb17b16329ee
-- title:
--   Lemma 4.4 — equal-weight packet and moment-preserving path: $n$ particle paths keep $K$ moments fixed, with length $\le C\sqrt{nB}+CBK^2\log(K+1)/\sqrt\eta$
-- statement:
--   There is an absolute constant $C_{path}$ with the following property. Let $B\ge 1$, $K\ge 2$, let $\nu_0,\nu_1$ be probability laws carried by at most $K+2$ points of $[0,B]$ with equal moments through degree $K$, and fix $0<\eta<1/10$. If $n\ge C_{path}\,\eta^{-1}BK^5\log^2(K+1)$, there are $n$ particle paths $x_i:[0,1]\to[0,B]$, piecewise continuously differentiable after taking square roots, such that the moments $\frac1n\sum_i x_i(t)^q=\frac1n\mathrm{tr}\,D_t^{2q}$, $0\le q\le K$, of the empirical law $\hat\nu_t=\frac1n\sum_i\delta_{x_i(t)}$ do not depend on $t$, and
--   $$L_K\le C_{path}\sqrt{nB}+\frac{C_{path}BK^2\log(K+1)}{\sqrt\eta},\qquad |h(\hat\nu_b)-h(\nu_b)|\le C_{path}\eta+\frac{C_{path}BK^2\log(K+1)}n\quad(b\in\{0,1\}),$$
--   where $D_t=\mathrm{diag}(\sqrt{x_1(t)},\dots,\sqrt{x_n(t)})$, $L_K$ is the path length (4.10) and $h(\mu)=\int\sqrt x\,d\mu$.
--
--   The lemma turns the abstract laws of Proposition 4.2 into actual $n\times n$ diagonal spectra joined by a path along which the first $K$ moments never move, which is what the Fisher–Rao comparison of Lemma 4.7 integrates.
--
--   **Formalization Note.** Paths are `x : Fin n → ℝ → ℝ` with values in $[0,B]$ on $[0,1]$; regularity is `SqrtPiecewiseC1`, the length is `pathLength`, and $h(\hat\nu_b)=\frac1n\sum_i\sqrt{x_i(b)}$. $C_{path}$ is chosen before all data.
--
--   Differences from the source:
--   - reading: ν_0, ν_1 supported on at most K + 2 points in [0, B] → probability measures carried by at most K + 2 points of [0, B]; reason: they are laws (the probability laws of Proposition 4.2, p. 15–16), approximated by the n-point empirical laws in (4.10a)
--   - reading: piecewise continuously differentiable after taking square roots → SqrtPiecewiseC1: a finite partition 0 = t_0 < … < t_r = 1 with √x_i C¹ on every closed piece; reason: the standard meaning; it gives continuity of √x_i on [0, 1]
--   - encoding: L_K = ∫_0^1 ((1/n) tr Ḋ_t²)^{1/2} dt → pathLength x: interval integral of √((1/n) Σ_i (deriv √x_i t)²); reason: deriv is the derivative off the finitely many joining times, a null set
--   - encoding: x_i : [0,1] → [0,B], moments independent of t → x : Fin n → ℝ → ℝ with x i t ∈ [0,B] for t ∈ [0,1], and (1/n) Σ_i x_i(t)^q = (1/n) Σ_i x_i(0)^q for t ∈ [0,1], q ≤ K; reason: functions on ℝ restricted to [0,1]; the same statement
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 16, Lemma 4.4, (4.9)–(4.10a) (proof pp. 41–52, A.4)

import Mathlib
import Definitions.Def_SchattenSketch_Main_Path

open MeasureTheory

namespace SchattenSketch.Main

/-- Lemma 4.4 (equal-weight packet and moment-preserving path; Yang, p. 16). There is an absolute
constant `C_path` such that: for `B ≥ 1`, `K ≥ 2`, probability laws `ν₀, ν₁` each carried by at
most `K + 2` points of `[0, B]` with equal moments through degree `K`, `0 < η < 1/10` and
`n ≥ C_path η⁻¹ B K⁵ log²(K + 1)`, there are `n` particle paths `xᵢ : [0, 1] → [0, B]`, piecewise
`C¹` after square roots, whose empirical moments `(1/n) ∑ᵢ xᵢ(t)^q`, `0 ≤ q ≤ K`, do not depend on
`t`, whose length satisfies (4.10), and whose endpoint square-root moments satisfy (4.10a). -/
theorem lemma_4_4 :
    ∃ C_path : ℝ, ∀ (B : ℝ) (K : ℕ) (ν₀ ν₁ : Measure ℝ),
      1 ≤ B → 2 ≤ K → IsProbabilityMeasure ν₀ → IsProbabilityMeasure ν₁ →
      IsSupportedOnAtMost ν₀ (K + 2) B → IsSupportedOnAtMost ν₁ (K + 2) B →
      (∀ q : ℕ, q ≤ K → ∫ x, x ^ q ∂ν₀ = ∫ x, x ^ q ∂ν₁) →
      ∀ η : ℝ, 0 < η → η < 1 / 10 →
      ∀ n : ℕ, C_path * η⁻¹ * B * (K : ℝ) ^ 5 * Real.log ((K : ℝ) + 1) ^ 2 ≤ n →
        ∃ x : Fin n → ℝ → ℝ,
          (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, x i t ∈ Set.Icc 0 B) ∧
          (∀ i, SqrtPiecewiseC1 (x i)) ∧
          (∀ q : ℕ, q ≤ K → ∀ t ∈ Set.Icc (0 : ℝ) 1,
            (1 / (n : ℝ)) * ∑ i, x i t ^ q = (1 / (n : ℝ)) * ∑ i, x i 0 ^ q) ∧
          pathLength x ≤ C_path * Real.sqrt (n * B) +
            C_path * B * (K : ℝ) ^ 2 * Real.log ((K : ℝ) + 1) / Real.sqrt η ∧
          |(1 / (n : ℝ)) * ∑ i, Real.sqrt (x i 0) - ∫ y, Real.sqrt y ∂ν₀| ≤
            C_path * η + C_path * B * (K : ℝ) ^ 2 * Real.log ((K : ℝ) + 1) / n ∧
          |(1 / (n : ℝ)) * ∑ i, Real.sqrt (x i 1) - ∫ y, Real.sqrt y ∂ν₁| ≤
            C_path * η + C_path * B * (K : ℝ) ^ 2 * Real.log ((K : ℝ) + 1) / n := by sorry

end SchattenSketch.Main
