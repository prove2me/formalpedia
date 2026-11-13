-- Prove2me | Theorems.Thm_TentNoise_lemma_B_8
-- name    : TentNoise.lemma_B_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:15.245184+00:00
-- url     : https://prove2.me/theorems/4751e98a-a6cd-4c41-99f6-944af28827b9
-- title:
--   Lemma B.8 — larger-noise path certificate: $D(\sigma)\ge d_0\min\{\sigma,1\}$ and $W\ge\tfrac16(d_0\min\{\sigma,1\}-\delta)$
-- statement:
--   Define
--
--   $$
--   D(\sigma)=\int_0^1\mathbb E\,|\mathfrak r(a+\sigma Z)-a|\,da,\qquad d_0=\frac{1-e^{-\pi^2/2}}{4\pi^2}>0 .
--   $$
--
--   Then
--
--   $$
--   D(\sigma)\ge d_0\min\{\sigma,1\}\qquad(\sigma\ge0).
--   $$
--
--   For the fitted map $g$ of Lemma B.3 (with $N=2^k$, $0<b\le1/32$), every $\sigma\ge0$ and every $T\ge1$ satisfy
--
--   $$
--   W_{1,\rho_{1,T}}\bigl(\mathbb P_T,\mathbb Q^{g,\sigma}_T\bigr)\ge\frac16\bigl(d_0\min\{\sigma,1\}-\delta\bigr),\qquad \delta=\|g-f\|_2 .
--   $$
--
--   When the noise is large, the noise increments themselves are visible on path space, since the true trajectories satisfy $X_{t+1}=f(X_t)$ exactly.
--
--   **Formalization Note** The right side of the second display enters through `ENNReal.ofReal`, so a negative value gives the trivial bound $0$.
--
--   Differences from the source:
--   - encoding: the fitted map g of Lemma B.3 with N = 2^k ('From now on take N = 2^k', p.28), a map [0,1] → [0,1]; paths in [0,1]^{T+1} → any g : ℝ → ℝ, measurable, with IsFitMap (2^k) b g (g ∘ h_0 = g ∘ h_1 = id on [0,1]) and 0 < b ≤ 1/32; paths Fin (T+1) → ℝ; reason: IsFitMap pins g down on [0,1] (Lemma B.3) and gives g([0,1]) = [0,1]; values of g off [0,1] are never visited; the paper's g extends to a Borel map of ℝ
--   - encoding: W_{1,ρ_{1,T}} as a real infimum over couplings → the published transport cost with cost ρ_{1,T}, valued in [0,∞], right-hand sides through ENNReal.ofReal; reason: Lean convention; the value is finite for the probability path laws compared, and equal to the paper's
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma B.8, p.31 (PDF p.31), eqs. (74)–(75)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_pathW1
import Definitions.Def_TentNoise_noisedLaw
import Definitions.Def_TentNoise_errP
import Definitions.Def_TentNoise_IsFitMap
import Definitions.Def_TentNoise_Dnoise

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma B.8 (A Lipschitz path certificate for larger noise)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.8, p.31,
eqs. (74)–(75)): with `D(σ) = ∫₀¹ E|𝔯(a + σZ) − a| da` and `d₀ = (1 − e^{−π²/2})/(4π²) > 0`,
`D(σ) ≥ d₀ min{σ, 1}` for `σ ≥ 0`; and for the fitted map of Lemma B.3, every `σ ≥ 0` and `T ≥ 1`,
`W_{1,ρ_{1,T}}(ℙ_T, ℚ^{g,σ}_T) ≥ (1/6)(d₀ min{σ, 1} − δ)`, `δ = ‖g − f‖₂`.

**Formalization Note** The fitted map is any `g` with `IsFitMap (2^k) b g`, `0 < b ≤ 1/32`, Borel on
`ℝ` (`N = 2^k`, the standing choice of Step 3, p.28). The right side of (75) enters through
`ENNReal.ofReal`, so a negative value gives the trivial bound `0`. -/
theorem lemma_B_8 :
    0 < (1 - Real.exp (-(Real.pi ^ 2 / 2))) / (4 * Real.pi ^ 2) ∧
    (∀ σ : ℝ, 0 ≤ σ →
      (1 - Real.exp (-(Real.pi ^ 2 / 2))) / (4 * Real.pi ^ 2) * min σ 1 ≤ Dnoise σ) ∧
    (∀ (k : ℕ) (b : ℝ), 0 < b → b ≤ 1 / 32 → ∀ (g : ℝ → ℝ) (hg : Measurable g),
      IsFitMap (2 ^ k) b g → ∀ σ : ℝ, 0 ≤ σ → ∀ T : ℕ, 1 ≤ T →
        ENNReal.ofReal (1 / 6 *
            ((1 - Real.exp (-(Real.pi ^ 2 / 2))) / (4 * Real.pi ^ 2) * min σ 1 - errP g)) ≤
          pathW1 T (trueLaw T) (noisedLaw g hg σ T)) := by sorry

end TentNoise
