-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_theorem_4_12
-- name    : RandTensorIso.Smoothed.theorem_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:37:14.451208+00:00
-- url     : https://prove2.me/theorems/804b4cfb-00c8-4d7e-bde4-bc47b5e5250f
-- title:
--   Theorem 4.12 — uniform repulsion of squared singular values of $F+M$, complex case
-- statement:
--   Let $\xi$ be a mean-zero, variance-one sub-Gaussian distribution on $\mathbb C$. Let $M$ be an $n\times p$ matrix with i.i.d. entries $m_{ij}\sim\xi$ and $p=\Theta(n^\zeta)$ for $\zeta\in(0,1)$, and let $F$ be an $n\times p$ matrix with arbitrary complex entries such that $\|F\|\le n^D$ for some $D\ge1/2$. Then there are constants $c,C>0$, depending only on $K_\xi,\chi_\xi,D,\zeta$, such that
--   $$\mathbb P\Big(\min_{1\le i<p}\big(\sigma_i(F+M)^2-\sigma_{i+1}(F+M)^2\big)\le cn^{1-4D}\Big)\le C\sqrt{\frac pn}.$$
--   Applied to the transposed flattenings of $F+M$ with $n^2$ rows and $p=n$ columns, it gives the eigenvalue gaps of the Gram matrices needed by Algorithm 3. In Lean the event is "some consecutive pair has gap $\le cn^{1-4D}$", bounded in outer measure, for all $n$, all $p$ with $an^\zeta\le p\le bn^\zeta$ and all $F$.
--
--   Differences from the source:
--   - reading: p = Θ(n^ζ); c, C depending only on K_ξ, χ_ξ, D, ζ → a n^ζ ≤ p ≤ b n^ζ for given 0 < a ≤ b; c, C chosen from (ζ, a, b, D, K, χ) before ξ, n, p, F; reason: Θ hides two constants on which c, C must be allowed to depend (in Theorem 2.14's use a = b = 1); uniform over ξ with K_ξ = K, χ_ξ = χ
--   - encoding: P(min_{1≤i<p} (σ_i² − σ_{i+1}²) ≤ c n^{1−4D}) → outer measure of {M : ∃ consecutive i, i+1 (0-based) with σ_i² − σ_{i+1}² ≤ c n^{1−4D}}; reason: the same event; empty when p = 1
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 59 (PDF 61), Theorem 4.12

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Spectral
import Definitions.Def_RandTensorIso_Smoothed_SubGaussian

open Matrix MeasureTheory

namespace RandTensorIso.Smoothed

/-- Theorem 4.12 (p. 59). For `ζ ∈ (0, 1)`, Θ-constants `0 < a ≤ b`, `D ≥ 1/2`, `K > 0`, `χ`,
there are `c, C > 0` such that for every mean-zero, variance-one sub-Gaussian `ξ` on `ℂ` with
`K_ξ = K` and `χ_ξ = χ`, all `n, p` with `a n^ζ ≤ p ≤ b n^ζ`, and every complex `n × p` matrix
`F` with `‖F‖ ≤ n^D`:
`P(min_{1 ≤ i < p} (σ_i(F + M)² − σ_{i+1}(F + M)²) ≤ c n^{1−4D}) ≤ C √(p/n)`
(`i` 0-based below, `i + 1 < p`). -/
theorem theorem_4_12 (ζ a b D K χ : ℝ) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (ha : 0 < a) (hab : a ≤ b)
    (hD : 1 / 2 ≤ D) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ξ : ProbabilityMeasure ℂ), IsStdSubGaussian (ξ : Measure ℂ) →
      subGaussConst (ξ : Measure ℂ) = K → chiConst (ξ : Measure ℂ) = χ →
      ∀ (n p : ℕ), a * (n : ℝ) ^ ζ ≤ p → (p : ℝ) ≤ b * (n : ℝ) ^ ζ →
      ∀ (F : Matrix (Fin n) (Fin p) ℂ), opNorm F ≤ (n : ℝ) ^ D →
        matrixLaw ξ n p {m | ∃ (i j : Fin p), j.val = i.val + 1 ∧
            sv (F + Matrix.of m) i ^ 2 - sv (F + Matrix.of m) j ^ 2 ≤ c * (n : ℝ) ^ (1 - 4 * D)} ≤
          ENNReal.ofReal (C * Real.sqrt (p / n)) := by sorry

end RandTensorIso.Smoothed
