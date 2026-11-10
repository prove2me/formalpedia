-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_lemma_4_7
-- name    : RandTensorIso.Smoothed.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:37:04.549384+00:00
-- url     : https://prove2.me/theorems/ed458d43-bb6d-473f-8efb-326e10dfbde9
-- title:
--   Lemma 4.7 (complex form, §4.4) — spectral window for the Gram matrix of $F+M$
-- statement:
--   Let $\xi$ be a mean-zero, variance-one sub-Gaussian distribution (on $\mathbb C$, §4.4). Let $M$ be an $n\times p$ matrix with i.i.d. entries $m_{ij}\sim\xi$ and $p\le n$, and let $F$ be a (complex) $n\times p$ matrix with $\|F\|\le n^D$ for some $D\ge1/2$. Then there are constants $c,C>0$, depending only on $K_\xi$, such that with probability at least $1-e^{-cp}$,
--   $$\big\|(F+M)^*(F+M)-(n+\sigma_{\min}(F)^2)I_p\big\|\le C\Big(\|F\|^2-\sigma_{\min}(F)^2+\sqrt p\,(\sqrt n+\|F\|)\Big).$$
--   In Lean, $c$ and $C$ are chosen from $K$ and work for every $\xi$ with $K_\xi=K$, every $D\ge1/2$, all $p\le n$ and every $F$; the probability of the complementary event is bounded by $e^{-cp}$.
--
--   Differences from the source:
--   - generalization: Lemma 4.7 for real ξ and real F with transposes → ξ on ℂ, complex F, adjoints, as §4.4 extends it; reason: §4.4 states the proof applies verbatim; real ξ (a law on ℝ ⊆ ℂ) and real F are special cases
--   - reading: constants c, C > 0 depending only on K_ξ → c, C chosen from K before ξ, D, n, p, F and valid for every ξ with K_ξ = K; reason: the uniform reading of 'depending only on K_ξ'
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 53 (PDF 55), Lemma 4.7; p. 59 (PDF 61), §4.4 (complex case)

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Spectral
import Definitions.Def_RandTensorIso_Smoothed_SubGaussian

open Matrix MeasureTheory

namespace RandTensorIso.Smoothed

/-- Lemma 4.7 (p. 53), complex form (§4.4, p. 59). For every `K > 0` there are `c, C > 0`
(depending only on `K_ξ = K`) such that for every mean-zero, variance-one sub-Gaussian `ξ` on `ℂ`
with `K_ξ = K`, every `D ≥ 1/2`, all `p ≤ n` and every complex `n × p` matrix `F` with
`‖F‖ ≤ n^D`, the event
`‖(F + M)^*(F + M) − (n + σ_min(F)²) I_p‖ > C(‖F‖² − σ_min(F)² + √p(√n + ‖F‖))`
has probability at most `e^{−cp}` (`M` with i.i.d. `ξ` entries). -/
theorem lemma_4_7 (K : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ξ : ProbabilityMeasure ℂ), IsStdSubGaussian (ξ : Measure ℂ) →
      subGaussConst (ξ : Measure ℂ) = K →
      ∀ (D : ℝ), 1 / 2 ≤ D → ∀ (n p : ℕ), p ≤ n →
      ∀ (F : Matrix (Fin n) (Fin p) ℂ), opNorm F ≤ (n : ℝ) ^ D →
        matrixLaw ξ n p {m | C * (opNorm F ^ 2 - sigmaMin F ^ 2 +
            Real.sqrt p * (Real.sqrt n + opNorm F)) <
          opNorm ((F + Matrix.of m)ᴴ * (F + Matrix.of m) -
            (((n : ℝ) + sigmaMin F ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ))} ≤
          ENNReal.ofReal (Real.exp (-(c * p))) := by sorry

end RandTensorIso.Smoothed
