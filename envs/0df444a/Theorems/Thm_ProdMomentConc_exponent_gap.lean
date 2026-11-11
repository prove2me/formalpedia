-- Prove2me | Theorems.Thm_ProdMomentConc_exponent_gap
-- name    : ProdMomentConc.exponent_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:29.87154+00:00
-- url     : https://prove2.me/theorems/23c3b3c3-0cb0-4ef9-a8f8-1060a0c1dfd4
-- title:
--   §A.1 — the Chernoff exponent at $\lambda_0$ and the read-degree gap
-- statement:
--   Let $0 < p < \alpha < 1$ and $0 < d_0 \le d$. Define
--
--   $$
--   F_c(\lambda) := \lambda\alpha - \frac{1}{c}\ln\big(1 - p + p e^{\lambda c}\big), \qquad z := \frac{\alpha(1-p)}{p(1-\alpha)}, \qquad \lambda_0 := \frac{1}{d_0}\ln z.
--   $$
--
--   Then:
--   1. $F_{d_0}(\lambda_0) = \frac{1}{d_0} D(\alpha\|p)$;
--   2. $F_{d_0}(\lambda_0) - F_d(\lambda_0) = \frac{1}{d}\ln\big(1 - p + p z^{d/d_0}\big) - \frac{1}{d_0}\ln(1 - p + p z)$;
--   3. $1 - p + p z^{d/d_0} \le z^{d/d_0 - 1}(1 - p + p z)$;
--   4. $F_{d_0}(\lambda_0) - F_d(\lambda_0) \le \big(\frac{1}{d_0} - \frac{1}{d}\big)\big(\ln z - \ln(1 - p + pz)\big)$;
--   5. $\big(\frac{1}{d_0} - \frac{1}{d}\big)\big(\ln z - \ln(1 - p + pz)\big) = \big(\frac{1}{d_0} - \frac{1}{d}\big)\ln\frac{\alpha}{p}$.
--
--   These estimates compare the Chernoff exponent of a read-$d_0$ family with that of a read-$d$ family at the point $\lambda_0$ optimal for $d_0$. They turn the bad term of the event $\Lambda_k > d_0$ into the factor $\exp\big(k(1/d_0 - 1/\Delta_L)\ln(\alpha/p)\big)$ appearing in condition (8).
--
--   **Formalization Note** $D(\alpha\|p)$ is the published binary relative entropy `LimitedPriceChanges.LowerBound.klBer α p`. $z^{d/d_0}$ and $z^{d/d_0-1}$ are real powers; $z > 1$ under the hypotheses. The five relations are one conjunction.
--
--   Differences from the source:
--   - generalization: d₀ ≤ d_L positive integers (and Lemma A.2 uses d = Δ_L) → real numbers 0 < d₀ ≤ d; reason: every integer instance is a real instance
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), §A.1 (proof of Theorem 3.2), p.32 (PDF p.32); reused in the proof of Lemma A.2, p.35

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL

namespace ProdMomentConc

/-- **Exponent estimates at the Chernoff point `λ₀`** (§A.1).
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), §A.1 (proof of Theorem 3.2), p.32.

With `F_d(λ) := λα − (1/d) ln(1 − p + p e^{λd})`, `z := α(1−p)/(p(1−α))` and `λ₀ := (1/d₀) ln z`,
for `0 < p < α < 1` and `0 < d₀ ≤ d`:
1. `F_{d₀}(λ₀) = (1/d₀) D(α‖p)`;
2. `F_{d₀}(λ₀) − F_d(λ₀) = (1/d) ln(1 − p + p z^{d/d₀}) − (1/d₀) ln(1 − p + pz)`;
3. `1 − p + p z^{d/d₀} ≤ z^{d/d₀ − 1}(1 − p + pz)`;
4. `F_{d₀}(λ₀) − F_d(λ₀) ≤ (1/d₀ − 1/d)(ln z − ln(1 − p + pz))`;
5. `(1/d₀ − 1/d)(ln z − ln(1 − p + pz)) = (1/d₀ − 1/d) ln(α/p)`.

**Formalization Note.** The paper's degree `dL` is `d` here, taken real with `0 < d₀ ≤ d` (the
paper's `d₀ ≤ dL` are positive integers; Lemma A.2 applies the same estimate with `d = ΔL`).
`D(α‖p)` is the published binary relative entropy
`LimitedPriceChanges.LowerBound.klBer α p = α ln(α/p) + (1 − α) ln((1 − α)/(1 − p))` (p.4).
Powers `z^{…}` are real powers (`Real.rpow`), with `z > 1` under the hypotheses. -/
theorem exponent_gap (α p d₀ d : ℝ) (hp : 0 < p) (hpα : p < α) (hα1 : α < 1)
    (hd₀ : 0 < d₀) (hd₀d : d₀ ≤ d) :
    let z : ℝ := α * (1 - p) / (p * (1 - α))
    let lam0 : ℝ := (1 / d₀) * Real.log z
    let F : ℝ → ℝ → ℝ := fun c s => s * α - (1 / c) * Real.log (1 - p + p * Real.exp (s * c))
    F d₀ lam0 = (1 / d₀) * LimitedPriceChanges.LowerBound.klBer α p ∧
    F d₀ lam0 - F d lam0 =
      (1 / d) * Real.log (1 - p + p * z ^ (d / d₀)) - (1 / d₀) * Real.log (1 - p + p * z) ∧
    1 - p + p * z ^ (d / d₀) ≤ z ^ (d / d₀ - 1) * (1 - p + p * z) ∧
    F d₀ lam0 - F d lam0 ≤ (1 / d₀ - 1 / d) * (Real.log z - Real.log (1 - p + p * z)) ∧
    (1 / d₀ - 1 / d) * (Real.log z - Real.log (1 - p + p * z)) =
      (1 / d₀ - 1 / d) * Real.log (α / p) := by sorry

end ProdMomentConc
