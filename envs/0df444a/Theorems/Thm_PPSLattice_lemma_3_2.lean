-- Prove2me | Theorems.Thm_PPSLattice_lemma_3_2
-- name    : PPSLattice.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:34:39.956859+00:00
-- url     : https://prove2.me/theorems/760dfff4-f42a-4350-8922-8dbbc566965f
-- title:
--   Lemma 3.2 — discrete Gaussian tail $\Pr[|x|>k\sigma]\le 2e^{-k^2/2}$
-- statement:
--   Let $\sigma>0$ and let $D_{\mathbb Z,\sigma}$ be the discrete Gaussian on $\mathbb Z$ with weights $\rho_\sigma(x)=e^{-x^2/(2\sigma^2)}$. For every $k>0$,
--   $$\Pr\bigl[|x|>k\sigma : x\leftarrow D_{\mathbb Z,\sigma}\bigr]\le 2\exp\Bigl(-\frac{k^2}{2}\Bigr).$$
--
--   This tail bound controls the LWE error $\mathbf e$ in the noise analysis of Construction 4.6 (Lemma 4.18): with overwhelming probability every entry of $\mathbf e$ is at most a slightly superconstant multiple of $\chi$.
--
--   Differences from the source:
--   - reading: D_{Z,σ} with width parameter σ (no formula) → weights exp(−x²/(2σ²)); reason: the convention of [Lyu12], the source of Lemma 3.2
--   - encoding: probability Pr[·] → the PMF's outer measure, in ℝ≥0∞; reason: same value
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Lemma 3.2 ([Lyu12, MP12]), p.16

import Mathlib
import Definitions.Def_PPSLattice_dGauss
set_option autoImplicit false

namespace PPSLattice

/-- **Lemma 3.2** (discrete Gaussian tail). For every width `σ > 0` and every `k > 0`,
`Pr[|x| > kσ : x ← D_{Z,σ}] ≤ 2 exp(−k²/2)`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Lemma 3.2 ([Lyu12, MP12]), p.16.

**Formalization Note.** `D_{Z,σ}` has weights `exp(−x²/(2σ²))` (the [Lyu12] convention); probabilities
are in `ℝ≥0∞`. -/
theorem lemma_3_2 (σ : ℝ) (hσ : 0 < σ) (k : ℝ) (hk : 0 < k) :
    (dGauss σ).toOuterMeasure {x : ℤ | k * σ < |(x : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(k ^ 2) / 2)) := by sorry

end PPSLattice
