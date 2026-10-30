-- Prove2me | Theorems.Thm_WassersteinDRO_GelbrichFiniteSample_true_risk_le_gelbrich_risk
-- name    : WassersteinDRO.GelbrichFiniteSample.true_risk_le_gelbrich_risk
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:01:45.584988+00:00
-- url     : https://prove2.me/theorems/8d24d657-c0ee-423f-8069-b07561a06b4d
-- title:
--   Eq. (18): $\mathcal R(\mathbb P, \ell) \le \overline{\mathcal R}_\varepsilon(\widehat\mu, \widehat\Sigma, \ell)$ for every $\mathbb P$ in the Gelbrich hull
-- statement:
--   Let $\Xi \subseteq \mathbb R^m$, $\varepsilon \in \mathbb R$, $\widehat\mu \in \mathbb R^m$ and let $\widehat\Sigma$ be an $m \times m$ matrix. Let $\mathbb P$ be a probability distribution on $\mathbb R^m$ supported on $\Xi$ (i.e. $\mathbb P(\Xi^{\mathrm c}) = 0$) that has mean vector $\mu$ and covariance matrix $\Sigma$ for some $(\mu, \Sigma) \in \mathcal U_\varepsilon(\widehat\mu, \widehat\Sigma)$. Then for every loss function $\ell : \mathbb R^m \to [-\infty, +\infty]$,
--
--   $$\mathcal R(\mathbb P, \ell) \le \overline{\mathcal R}_\varepsilon(\widehat\mu, \widehat\Sigma, \ell) = \sup_{\mathbb Q \in \mathbb G_\varepsilon(\widehat\mu, \widehat\Sigma)} \mathcal R(\mathbb Q, \ell).$$
--
--   This is the deterministic half of the finite sample guarantee (29a): on the event of Theorem 21, the true distribution lies in the Gelbrich hull, and then its risk is bounded by the Gelbrich risk simultaneously for all losses.
--
--   Differences from the source:
--   - reading: the display (18) defining R̄ε(µ̂, Σ̂, ℓ) as a supremum over Gε(µ̂, Σ̂) → its consequence R(P, ℓ) ≤ R̄ε(µ̂, Σ̂, ℓ) for every P in the hull; reason: this is the property of (18) that the paper's guarantee (29a) relies on; the definition itself is the gelbrichRisk item.
--   - generalization: measurable losses ℓ ∈ L satisfying Assumption 1 (p. 1, p. 9) → every function ℓ : ℝ^m → [−∞, +∞]; reason: the bound holds for every function and specializes to the paper's losses.
--   - generalization: Σ̂ ∈ S^m_+ (standing assumption of §2.3, p. 16), Ξ closed (p. 6), ε ≥ 0 → any matrix Σ̂, any set Ξ, any real ε; reason: the bound holds for all of them and specializes to the paper's setting.
--   - encoding: P ∈ Gε(µ̂, Σ̂) → P a probability measure with P(Ξᶜ) = 0 and HasMeanCov P µ Σ for some (µ, Σ) ∈ Uε(µ̂, Σ̂); reason: this is Definition 2 unfolded; HasMeanCov includes the finite second moments that a covariance matrix presupposes.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §2.3, eq. (18), p. 18 (unnumbered step used in Theorem 22, p. 23)

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_risk
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_HasMeanCov
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_uncertaintySet
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_gelbrichRisk

open MeasureTheory

namespace WassersteinDRO.GelbrichFiniteSample

/-- **The Gelbrich risk bounds the risk of every member of the hull (eq. (18)).**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §2.3, eq. (18), p. 18 (unnumbered step): "To show this, we define the Gelbrich risk as
R̄_ε(µ̂, Σ̂, ℓ) = sup_{Q∈G_ε(µ̂,Σ̂)} R(Q, ℓ) (18)". This is the step of (29a) (Theorem 22, p. 23)
that turns membership of the true distribution in the Gelbrich hull into the risk bound.

For every `Ξ ⊆ ℝ^m`, `ε ∈ ℝ`, `µ̂ ∈ ℝ^m`, `m × m` matrix `Σ̂`, every probability measure `P` on `ℝ^m`
with `P(Ξᶜ) = 0` that has mean `µ` and covariance `Σ` for some `(µ, Σ) ∈ U_ε(µ̂, Σ̂)`, and every loss
`ℓ : ℝ^m → [−∞, +∞]`: `R(P, ℓ) ≤ R̄_ε(µ̂, Σ̂, ℓ)`.

**Formalization Note.** No measurability of `ℓ` and no condition on `Σ̂` or `Ξ` is needed for this
step, so none is assumed; the statement covers the paper's measurable losses, `Σ̂ ∈ S^m_+` and closed
`Ξ`. "Supported on Ξ" is `P(Ξᶜ) = 0`. -/
theorem true_risk_le_gelbrich_risk {m : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin m))) (ε : ℝ)
    (μh : EuclideanSpace ℝ (Fin m)) (Sigh : Matrix (Fin m) (Fin m) ℝ)
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P] (hPΞ : P Ξᶜ = 0)
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) (hP : HasMeanCov P μ Sig)
    (hU : (μ, Sig) ∈ uncertaintySet ε μh Sigh) (ℓ : EuclideanSpace ℝ (Fin m) → EReal) :
    risk P ℓ ≤ gelbrichRisk Ξ ε μh Sigh ℓ := by sorry

end WassersteinDRO.GelbrichFiniteSample
