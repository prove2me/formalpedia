-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_lemma_4_9
-- name    : RandTensorIso.Smoothed.lemma_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:37:31.656927+00:00
-- url     : https://prove2.me/theorems/477248f6-0f82-4af9-bc6e-38d2527d8342
-- title:
--   Lemma 4.9 (complex form, §4.4) — incompressibility of the right singular vectors of $F+M$
-- statement:
--   Let $\xi$ be a mean-zero, variance-one sub-Gaussian distribution (on $\mathbb C$). Let $M$ be an $n\times p$ matrix with i.i.d. entries $m_{ij}\sim\xi$ and $p=\Theta(n^\zeta)$ for $\zeta\in(0,1)$, and let $F$ be a (complex) $n\times p$ matrix with $\|F\|\le n^D$ for some $D\ge1/2$. Then there is $c>0$, depending only on $K_\xi$, such that for sufficiently large $n$, with probability at least $1-e^{-cp}$, every unit eigenvector of $(F+M)^*(F+M)$ lies in $\mathrm{Incomp}_p(c,\tau)$, where
--   $$\tau=\frac{c\sqrt p\,(\sqrt n+\sigma_{\min}(F))}{\|F\|^2-\sigma_{\min}(F)^2+\sqrt p\,(\sqrt n+\|F\|)} .$$
--   In Lean: $c$ is chosen from $K$; then for every $\zeta\in(0,1)$, Θ-constants $0<a\le b$ and $D\ge1/2$ there is $N_0$ such that for every $\xi$ with $K_\xi=K$, all $n\ge N_0$, all $p$ with $an^\zeta\le p\le bn^\zeta$ and every $F$, the set of $M$ for which some unit eigenvector lies outside $\mathrm{Incomp}_p(c,\tau)$ has outer probability at most $e^{-cp}$.
--
--   Differences from the source:
--   - generalization: Lemma 4.9 for real ξ and F with transposes and Incomp over ℝ^p → ξ on ℂ, complex F, adjoints, Definition 4.8 over ℂ^p, as §4.4 extends it; reason: §4.4 states the proof applies verbatim; real data are a special case, and a real unit eigenvector is compressible over ℂ^p iff over ℝ^p (real parts of a sparse approximant)
--   - reading: p = Θ(n^ζ) → a n^ζ ≤ p ≤ b n^ζ for given constants 0 < a ≤ b; reason: Θ made explicit
--   - reading: c depending only on K_ξ, for sufficiently large n → c chosen from K before ζ, a, b, D, ξ; the threshold N₀ chosen from (K, ζ, a, b, D) before ξ; reason: the uniform reading; the threshold may depend on the parameters of the statement but not on ξ beyond K_ξ, nor on F
--   - reading: with probability at least 1 − e^{-cp} → outer measure of the failure set ≤ e^{-cp}; reason: the event quantifies over all eigenvectors and need not be measurable; the outer-measure form is the stronger reading
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 54 (PDF 56), Lemma 4.9; p. 59 (PDF 61), §4.4 (complex case)

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Spectral
import Definitions.Def_RandTensorIso_Smoothed_SubGaussian

open Matrix MeasureTheory

namespace RandTensorIso.Smoothed

/-- Lemma 4.9 (p. 54), complex form (§4.4, p. 59). For every `K > 0` there is `c > 0` (depending
only on `K_ξ = K`) such that for every `ζ ∈ (0, 1)`, Θ-constants `0 < a ≤ b`, `D ≥ 1/2`, and all
sufficiently large `n` (`n ≥ N₀`): for every mean-zero, variance-one sub-Gaussian `ξ` on `ℂ` with
`K_ξ = K`, every `p` with `a n^ζ ≤ p ≤ b n^ζ` and every complex `n × p` `F` with `‖F‖ ≤ n^D`,
with probability at least `1 − e^{−cp}` every unit eigenvector of `(F + M)^*(F + M)` lies in
`Incomp_p(c, τ)`, `τ = c√p(√n + σ_min(F)) / (‖F‖² − σ_min(F)² + √p(√n + ‖F‖))`. The failure set
is bounded in outer measure. -/
theorem lemma_4_9 (K : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ζ a b D : ℝ), 0 < ζ → ζ < 1 → 0 < a → a ≤ b → 1 / 2 ≤ D →
      ∃ N₀ : ℕ, ∀ (ξ : ProbabilityMeasure ℂ), IsStdSubGaussian (ξ : Measure ℂ) →
        subGaussConst (ξ : Measure ℂ) = K →
        ∀ (n p : ℕ), N₀ ≤ n → a * (n : ℝ) ^ ζ ≤ p → (p : ℝ) ≤ b * (n : ℝ) ^ ζ →
        ∀ (F : Matrix (Fin n) (Fin p) ℂ), opNorm F ≤ (n : ℝ) ^ D →
          matrixLaw ξ n p {m | ∃ v : Fin p → ℂ, vecNorm v = 1 ∧
              (∃ μ : ℂ, ((F + Matrix.of m)ᴴ * (F + Matrix.of m)) *ᵥ v = μ • v) ∧
              ¬ Incomp c (c * Real.sqrt p * (Real.sqrt n + sigmaMin F) /
                  (opNorm F ^ 2 - sigmaMin F ^ 2 + Real.sqrt p * (Real.sqrt n + opNorm F))) v} ≤
            ENNReal.ofReal (Real.exp (-(c * p))) := by sorry

end RandTensorIso.Smoothed
