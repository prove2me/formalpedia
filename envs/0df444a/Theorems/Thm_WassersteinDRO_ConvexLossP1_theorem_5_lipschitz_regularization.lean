-- Prove2me | Theorems.Thm_WassersteinDRO_ConvexLossP1_theorem_5_lipschitz_regularization
-- name    : WassersteinDRO.ConvexLossP1.theorem_5_lipschitz_regularization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:53:19.251547+00:00
-- url     : https://prove2.me/theorems/6716f62c-bc61-4e4c-9c18-5a8e87d35717
-- title:
--   Theorem 5 (Lipschitz regularization): $\mathcal R_{\varepsilon,p}(\mathbb P, \ell) \le \mathcal R(\mathbb P, \ell) + \varepsilon \cdot \mathrm{Lip}(\ell)$
-- statement:
--   Let $(E, \|\cdot\|)$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra, let $p \ge 1$, $\varepsilon \ge 0$, and let $\Xi \subseteq E$ be closed. Let $\mathbb P$ be a Borel probability measure on $E$ (the nominal distribution), and let $\ell : E \to [-\infty, +\infty]$ be a measurable loss function satisfying the paper's Assumption 1: $\ell$ is upper semicontinuous and
--   $$\int_E |\ell(\xi)| \, \mathbb P(\mathrm d\xi) < \infty.$$
--   Then the worst-case risk over the type-$p$ Wasserstein ball is bounded by the Lipschitz-regularized nominal risk:
--   $$\mathcal R_{\varepsilon,p}(\mathbb P, \ell) \le \mathcal R(\mathbb P, \ell) + \varepsilon \cdot \mathrm{Lip}(\ell).$$
--
--   No convexity is assumed. When $\mathrm{Lip}(\ell) = \infty$ and $\varepsilon > 0$ the right side is $+\infty$; when $\varepsilon = 0$ the right side is $\mathcal R(\mathbb P, \ell)$. The bound is the upper half of Theorem 10, where it becomes an equality for convex losses, $p = 1$, $\Xi = \mathbb R^m$ and the empirical nominal distribution.
--
--   **Formalization Note** The product $\varepsilon \cdot \mathrm{Lip}(\ell)$ is computed in $[-\infty, +\infty]$ with $0 \cdot \infty = 0$. The risk uses the paper's expectation convention (see the definition of the risk).
--
--   Differences from the source:
--   - generalization: the nominal distribution P̂N (empirical or elliptical, Example 1, p. 2) → any Borel probability measure P satisfying Assumption 1 with respect to P; reason: the bound holds for every nominal distribution and specializes to both models of Example 1.
--   - generalization: Ξ known to contain the support of the distributions (p. 6) → no condition relating P and Ξ; reason: dropping the condition only enlarges the set of instances; the paper's instances are among them.
--   - reading: ε · Lip(ℓ) for ε = 0 and Lip(ℓ) = ∞ → 0 · ∞ = 0 (EReal); reason: the paper allows ε ≥ 0 (p. 6) and Lip(ℓ) = ∞ (p. 9) without defining the product; 0 · ∞ = 0 is the reading under which the ε = 0 case is meaningful (the ball is then the centre alone).
--   - encoding: R^m with an arbitrary norm → a finite-dimensional real normed space E; reason: same instances up to linear isometry.
--   - encoding: E^P[ℓ(ξ)] = ∞ when both parts are infinite (p. 2) → the definition `risk` (positive-part integral ∞ gives +∞, otherwise positive minus negative part); reason: the paper's convention written out.
--   - encoding: P(Ξ), distributions supported on Ξ → Borel probability measures Q with Q(Ξᶜ) = 0; reason: the standard meaning of "supported on Ξ".
--   - encoding: |ϕ(ξ) − ϕ(ξ′)| undefined when both values are the same infinity → valued ∞ in `lipModulus`; reason: changes no value when ℓ has a finite value, which Assumption 1 guarantees.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Theorem 5, p. 9; Assumption 1, p. 9

import Mathlib
import Definitions.Def_WassersteinDRO_ConvexLossP1_worstCaseRisk
import Definitions.Def_WassersteinDRO_ConvexLossP1_lipModulus

open MeasureTheory

namespace WassersteinDRO.ConvexLossP1

/-- **Theorem 5 (Lipschitz regularization).**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Theorem 5, p. 9: "The worst-case risk (6) of any fixed loss function ℓ ∈ L is bounded above by
the Lipschitz-regularized nominal risk, that is, R_{ε,p}(P̂N, ℓ) ≤ R(P̂N, ℓ) + ε · Lip(ℓ)."
Standing hypothesis, Assumption 1 (Regularity), p. 9, "tacitly assumed to hold throughout the rest
of the paper": "Any loss function ℓ ∈ L is upper semicontinuous and integrable with respect to the
nominal distribution P̂N, that is, ∫_{R^m} |ℓ(ξ)| P̂N(dξ) < ∞." Loss functions are measurable and
extended real-valued (p. 1); `Ξ` is closed and `ε ≥ 0` (p. 6); `p ∈ [1, ∞)` (Definition 1, p. 3).

For every `p ≥ 1`, `ε ≥ 0`, closed `Ξ ⊆ E`, Borel probability measure `P` (the nominal
distribution) and measurable, upper semicontinuous `ℓ : E → [−∞, ∞]` with `∫ |ℓ| dP < ∞`:
`R_{ε,p}(P, ℓ) ≤ R(P, ℓ) + ε · Lip(ℓ)`.

**Formalization Note.** The nominal distribution is any Borel probability measure `P` (the paper
uses `P̂_N` for the empirical or the elliptical nominal distribution of Example 1, p. 2). The
product `ε · Lip(ℓ)` is computed in `EReal`, where `0 · ∞ = 0`; for `ε > 0` and `Lip(ℓ) = ∞` the
right side is `+∞` (the paper: "If … Lip(ℓ) = ∞, then Theorem 5 is trivially satisfied"). No
convexity, Lipschitz continuity or finiteness of `ℓ` is assumed. Conventions of `risk`,
`ambiguityBall` and `lipModulus` are those of their definitions. -/
theorem theorem_5_lipschitz_regularization {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {p : ℝ} (hp : 1 ≤ p) {ε : ℝ} (hε : 0 ≤ ε) {Ξ : Set E} (hΞ : IsClosed Ξ)
    (P : Measure E) [IsProbabilityMeasure P] (ℓ : E → EReal) (hmeas : Measurable ℓ)
    (husc : UpperSemicontinuous ℓ) (hint : ∫⁻ ξ, EReal.abs (ℓ ξ) ∂P < ⊤) :
    worstCaseRisk ε p P Ξ ℓ ≤
      risk P ℓ + (ε : EReal) * ((lipModulus ℓ : ENNReal) : EReal) := by sorry

end WassersteinDRO.ConvexLossP1
