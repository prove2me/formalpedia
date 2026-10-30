-- Prove2me | Theorems.Thm_WassersteinDRO_StrongDuality_theorem_7_strong_duality
-- name    : WassersteinDRO.StrongDuality.theorem_7_strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:00:21.716005+00:00
-- url     : https://prove2.me/theorems/00cb54ab-0b1b-4f9a-8132-7565839187be
-- title:
--   Theorem 7 (Strong duality) (corrected: ε = 0 needs E[ℓ_γ] < ∞ for some γ)
-- statement:
--   Let $(E, \|\cdot\|)$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra (the paper's $\mathbb R^m$ with an arbitrary norm). Let $p \ge 1$, let $\Xi \subseteq E$ be closed, let $\mathbb P$ be a Borel probability measure on $E$ with $\mathbb P(E \setminus \Xi) = 0$ (the nominal distribution $\widehat{\mathbb P}_N$), and let $\ell : E \to [-\infty, +\infty]$ be upper semicontinuous with $\int |\ell| \, \mathrm d\mathbb P < \infty$ (Assumption 1 of the paper). Let $\varepsilon \ge 0$, and if $\varepsilon = 0$ assume in addition that $\mathbb E^{\mathbb P}[\ell_{\gamma}(\xi)] < \infty$ for some $\gamma \ge 0$. Then the worst-case risk over the type-$p$ Wasserstein ball of radius $\varepsilon$ around $\mathbb P$ satisfies
--   $$\mathcal R_{\varepsilon,p}(\mathbb P, \ell) = \sup_{\mathbb Q \in \mathbb B_{\varepsilon,p}(\mathbb P)} \mathbb E^{\mathbb Q}[\ell(\xi)] = \inf_{\gamma \ge 0} \; \mathbb E^{\mathbb P}[\ell_\gamma(\xi)] + \gamma \varepsilon^p,$$
--   where $\ell_\gamma(\xi) = \sup_{z \in \Xi} \ell(z) - \gamma \|z - \xi\|^p$ is the Moreau–Yosida regularization of $\ell$. Both sides take values in $[-\infty, +\infty]$; expectations follow the paper's convention ($+\infty$ when the positive part is not integrable).
--
--   The identity turns the worst-case risk, a supremum over an infinite-dimensional set of distributions, into a one-dimensional minimization over the multiplier $\gamma$ of an expectation under the nominal distribution. It is the starting point of the paper's tractable reformulations for piecewise concave and quadratic losses.
--
--   **Formalization Note** At $\varepsilon = 0$ the printed statement is false: on $\mathbb R$ with $p = 1$, $\Xi = \mathbb R$, $\mathbb P = \delta_0$ and $\ell(\xi) = \xi^2$ the left side is $0$ while $\ell_\gamma \equiv +\infty$ for every $\gamma \ge 0$. The added condition is no restriction for $\varepsilon > 0$, and for $\varepsilon = 0$ it is necessary and sufficient for the identity.
--
--   Differences from the source:
--
--   - correction: (10) for every radius ε ≥ 0 (p. 6) → hypothesis hcorr : 0 < ε ∨ ∃ γ ≥ 0, risk P ℓ_γ < ⊤; reason: false at ε = 0: E = ℝ, |·|, p = 1, Ξ = ℝ, P̂N = δ_0 (N = 1, empirical), ℓ(ξ) = ξ² (continuous, ∫|ℓ| dδ_0 = 0); the ball is {δ_0}, so the left side is 0, while ℓ_γ(0) = sup_z z² − γ|z| = +∞ for every γ ≥ 0, so the right side is +∞. For ε = 0 the disjunct is necessary and sufficient (ℓ_γ decreases to ℓ on Ξ by upper semicontinuity, monotone convergence), for ε > 0 it is no condition
--   - generalization: the nominal distribution P̂N (empirical (3) or elliptical (4), Example 1, p. 2) → any Borel probability measure P on E with P(Ξᶜ) = 0; reason: the paper's nominals are instances; the statement specializes to them
--   - reading: Ξ closed, 'known to contain the support of P' (p. 6); P̂N built from samples of P → hypothesis hPΞ : P Ξᶜ = 0 on the nominal distribution; reason: p. 6 calls B_{ε,p}(P̂N) the ball 'in P(Ξ) centered at the nominal distribution P̂N', so the centre is a distribution supported on Ξ; the empirical nominal (3) is supported on Ξ because its samples are, and §2.3 uses elliptical nominals only with Ξ = R^m. Without it (10) fails (Ξ = (−∞, 0], P̂N = δ_1, p = 1, ε = 1/2, ℓ(ξ) = ξ², the ball is empty so the left side is −∞, while ℓ_γ(1) = +∞ for every γ ≥ 0 so the right side is +∞)
--   - encoding: R^m with an arbitrary norm ‖·‖ → a finite-dimensional real normed space E with its Borel σ-algebra; reason: the same instances up to linear isometry
--   - encoding: P(Ξ), the probability distributions supported on Ξ → Borel probability measures Q with Q Ξᶜ = 0; reason: same objects for closed Ξ
--   - encoding: E^Q[ℓ(ξ)] = ∞ when both parts are infinite (p. 2); sup and inf of extended real values → the definition risk; ⨆ and ⨅ in EReal; reason: the paper's convention written out; the complete lattice [−∞, ∞] has no junk values
--   - encoding: Assumption 1 (p. 9, tacitly assumed throughout) and the measurable loss of p. 1 → hypotheses husc : UpperSemicontinuous ℓ and hint : ∫⁻ |ℓ| dP < ⊤; no separate measurability hypothesis; reason: the paper's standing assumptions made explicit; upper semicontinuity implies Borel measurability
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Theorem 7, eq. (10), p. 10; Assumption 1, p. 9; §1, p. 6 (Ξ, ball, (6))

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_worstCaseRisk
import Definitions.Def_WassersteinDRO_StrongDuality_moreauYosida

open MeasureTheory

namespace WassersteinDRO.StrongDuality

/-- **Theorem 7 (Strong duality), corrected at `ε = 0`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Theorem 7, eq. (10), p. 10: "The worst-case risk (6) of any fixed ℓ ∈ L satisfies
Rε,p(P̂N, ℓ) = inf_{γ≥0} E^{P̂N}[ℓγ(ξ)] + γε^p, (10)
where ℓγ(ξ) = sup_{z∈Ξ} ℓ(z) − γ‖z − ξ‖^p is a Moreau-Yosida regularization [77] of ℓ(ξ)."

Let `p ≥ 1`, `Ξ` closed (p. 6), `P` a Borel probability measure with `P(Ξᶜ) = 0`, and
`ℓ : E → [−∞, ∞]` upper semicontinuous with `∫ |ℓ| dP < ∞` (Assumption 1, p. 9, tacit throughout
the paper). Let `ε ≥ 0`, and if `ε = 0` assume `E^P[ℓ_γ] < ∞` for some `γ ≥ 0`. Then
`R_{ε,p}(P, ℓ) = inf_{γ ≥ 0} E^P[ℓ_γ(ξ)] + γ ε^p`, both sides in `[−∞, ∞]`.

**Formalization Note.**
- *Correction at `ε = 0`.* The printed theorem allows the radius `ε = 0` (p. 6) and is false there:
  on `ℝ` with `p = 1`, `Ξ = ℝ`, `P = δ₀` and `ℓ(ξ) = ξ²` the left side is `0` and `ℓ_γ ≡ +∞` for every
  `γ ≥ 0`. The hypothesis `hcorr` excludes exactly this: for `ε > 0` it is no condition, and for
  `ε = 0` it is necessary and sufficient for the identity.
- *Nominal distribution.* `P` is any Borel probability measure supported on `Ξ`; the paper's
  empirical (3) and elliptical (4) nominals are instances. `P(Ξᶜ) = 0` reads "Ξ is known to contain
  the support of P" (p. 6) for the nominal built from samples of P.
- *Space.* `(ℝ^m, ‖·‖)` with an arbitrary norm is a finite-dimensional real normed space `E`.
- *Conventions.* Expectations follow the paper's convention (`risk`: `+∞` when the positive part is
  not integrable); suprema and infima are in `EReal`; `W_p` is `[0, ∞]`-valued. Measurability of
  `ℓ` is implied by upper semicontinuity. -/
theorem theorem_7_strong_duality {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {p : ℝ} (hp : 1 ≤ p) {Ξ : Set E} (hΞ : IsClosed Ξ)
    (P : Measure E) [IsProbabilityMeasure P] (hPΞ : P Ξᶜ = 0)
    (ℓ : E → EReal) (husc : UpperSemicontinuous ℓ) (hint : ∫⁻ ξ, EReal.abs (ℓ ξ) ∂P < ⊤)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcorr : 0 < ε ∨ ∃ γ : ℝ, 0 ≤ γ ∧ risk P (moreauYosida ℓ Ξ γ p) < ⊤) :
    worstCaseRisk ε p P Ξ ℓ
      = ⨅ (γ : ℝ) (_ : 0 ≤ γ), risk P (moreauYosida ℓ Ξ γ p) + ((γ * ε ^ p : ℝ) : EReal) := by sorry

end WassersteinDRO.StrongDuality
