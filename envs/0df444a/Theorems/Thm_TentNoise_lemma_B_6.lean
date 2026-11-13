-- Prove2me | Theorems.Thm_TentNoise_lemma_B_6
-- name    : TentNoise.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:07.215043+00:00
-- url     : https://prove2.me/theorems/ff2ab392-22d9-46f7-958c-8ea4d5e776c0
-- title:
--   Lemma B.6 — time-shifting: $\mathbb E[\varphi(Y_0)\psi(Y_m)]=-\tfrac b4e^{-\pi^2\sigma^2(4N^2-1)/6}+R$, $|R|\le2b^2$
-- statement:
--   Take $N=2^k$, $m=k+1$, $\varphi(x)=x-\tfrac12$, $\psi(x)=\cos(\pi x)$, and let $g$ be the fitted map of Lemma B.3 ($0<b\le1/32$). For the fitted noisy path $(Y_t)\sim\mathbb Q^{g,\sigma}_T$ and every $\sigma\ge0$,
--
--   $$
--   \mathbb E\bigl[\varphi(Y_0)\psi(Y_m)\bigr]=-\frac b4\,e^{-\pi^2\sigma^2(4N^2-1)/6}+R,\qquad |R|\le2b^2 .
--   $$
--
--   For the true deterministic path $(X_t)\sim\mathbb P_T$,
--
--   $$
--   \mathbb E\bigl[\varphi(X_0)\psi(X_m)\bigr]=0 .
--   $$
--
--   In particular, if $0\le\sigma\le1/(4N)$, the two expectations differ by at least $b/16$ in absolute value.
--
--   A Lipschitz test of two coordinates, $m$ steps apart, thus separates the fitted noisy dynamics from the true ones at small noise.
--
--   **Formalization Note** The expectations are taken under the path laws at any horizon $T\ge m$, reading coordinates $0$ and $m$. $|R|\le2b^2$ is written as the distance between the expectation and the leading term.
--
--   Differences from the source:
--   - encoding: the fitted map g of Lemma B.3 with N = 2^k ('From now on take N = 2^k', p.28), a map [0,1] → [0,1]; paths in [0,1]^{T+1} → any g : ℝ → ℝ, measurable, with IsFitMap (2^k) b g (g ∘ h_0 = g ∘ h_1 = id on [0,1]) and 0 < b ≤ 1/32; paths Fin (T+1) → ℝ; reason: IsFitMap pins g down on [0,1] (Lemma B.3) and gives g([0,1]) = [0,1]; values of g off [0,1] are never visited; the paper's g extends to a Borel map of ℝ
--   - encoding: E[φ(Y_0)ψ(Y_m)] = −(b/4)e^{…} + R, |R| ≤ 2b²; expectations of the path (Y_t), (X_t) → |E − (−(b/4)e^{…})| ≤ 2b², with E the integral of (p_0 − 1/2)cos(π p_m) under ℚ^{g,σ}_T resp. ℙ_T for any T ≥ m; reason: R is defined as the difference; the two-time marginals do not depend on T ≥ m
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma B.6, pp.29–30 (PDF pp.29–30), eqs. (68)–(69)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_noisedLaw
import Definitions.Def_TentNoise_IsFitMap

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma B.6 (Time-shifting to match frequency)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.6, pp.29–30,
eqs. (68)–(69)): with `N = 2^k`, `m = k + 1`, `φ(x) = x − 1/2`, `ψ(x) = cos(πx)`, for the fitted map
and every `σ ≥ 0`, `E[φ(Y₀)ψ(Y_m)] = −(b/4) e^{−π²σ²(4N²−1)/6} + R` with `|R| ≤ 2b²`; for the true
deterministic path `E[φ(X₀)ψ(X_m)] = 0`; in particular, if `0 ≤ σ ≤ 1/(4N)`, the expectation gap is at
least `b/16` in absolute value.

**Formalization Note** `g` is Lemma B.3's map (`IsFitMap (2^k) b g`, `0 < b ≤ 1/32`), Borel on `ℝ`.
`(Y_t) ∼ ℚ^{g,σ}_T` and `(X_t) ∼ ℙ_T` for any horizon `T ≥ m`; the expectations read coordinates `0` and
`m`. `|R| ≤ 2b²` is written as the distance from the leading term. -/
theorem lemma_B_6 (k : ℕ) (b : ℝ) (hb0 : 0 < b) (hb : b ≤ 1 / 32) (g : ℝ → ℝ) (hg : Measurable g)
    (hfit : IsFitMap (2 ^ k) b g) (σ : ℝ) (hσ : 0 ≤ σ) (T : ℕ) (hT : k + 1 ≤ T) :
    |∫ p, (p 0 - 1 / 2) * Real.cos (Real.pi * p ⟨k + 1, by omega⟩) ∂(noisedLaw g hg σ T) -
        (-(b / 4) * Real.exp (-(Real.pi ^ 2 * σ ^ 2 * (4 * ((2 : ℝ) ^ k) ^ 2 - 1)) / 6))| ≤ 2 * b ^ 2 ∧
    ∫ p, (p 0 - 1 / 2) * Real.cos (Real.pi * p ⟨k + 1, by omega⟩) ∂(trueLaw T) = 0 ∧
    (σ ≤ 1 / (4 * (2 : ℝ) ^ k) →
      b / 16 ≤ |∫ p, (p 0 - 1 / 2) * Real.cos (Real.pi * p ⟨k + 1, by omega⟩) ∂(noisedLaw g hg σ T) -
        ∫ p, (p 0 - 1 / 2) * Real.cos (Real.pi * p ⟨k + 1, by omega⟩) ∂(trueLaw T)|) := by sorry

end TentNoise
