-- Prove2me | Theorems.Thm_WassersteinDRO_ConvexLossP1_theorem_10_convex_loss_p_one
-- name    : WassersteinDRO.ConvexLossP1.theorem_10_convex_loss_p_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:55:41.623032+00:00
-- url     : https://prove2.me/theorems/de966a18-6f6b-4bdb-a320-2d4e48128313
-- title:
--   Theorem 10 (Convex loss and $p = 1$): $\mathcal R_{\varepsilon,1}(\widehat{\mathbb P}_N, \ell) = \mathcal R(\widehat{\mathbb P}_N, \ell) + \varepsilon \, \mathrm{Lip}(\ell)$
-- statement:
--   Let $(E, \|\cdot\|)$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra (the paper's $\mathbb R^m$ with an arbitrary norm), and take $\Xi = E$. Let $N \ge 1$ and let $\widehat\xi_1, \dots, \widehat\xi_N \in E$ be samples (repetitions allowed) with empirical distribution $\widehat{\mathbb P}_N = \frac1N \sum_{i=1}^N \delta_{\widehat\xi_i}$. Let $\ell : E \to [-\infty, +\infty]$ be a convex, measurable loss function that satisfies the paper's Assumption 1: $\ell$ is upper semicontinuous and
--   $$\int_E |\ell(\xi)| \, \widehat{\mathbb P}_N(\mathrm d\xi) < \infty.$$
--   Then for every $\varepsilon \ge 0$ the worst-case risk over the type-1 Wasserstein ball coincides with the Lipschitz-regularized empirical loss:
--   $$\mathcal R_{\varepsilon,1}(\widehat{\mathbb P}_N, \ell) = \sup_{\mathbb Q :\, W_1(\mathbb Q, \widehat{\mathbb P}_N) \le \varepsilon} \mathbb E^{\mathbb Q}[\ell(\xi)] = \mathcal R(\widehat{\mathbb P}_N, \ell) + \varepsilon \, \mathrm{Lip}(\ell),$$
--   where the supremum is over all Borel probability measures $\mathbb Q$ on $E$.
--
--   No Lipschitz continuity or finiteness of $\ell$ is assumed: if $\mathrm{Lip}(\ell) = \infty$ and $\varepsilon > 0$ both sides are $+\infty$. The theorem shows that the upper bound of Theorem 5 is exact for convex losses with $p = 1$ and $\Xi = \mathbb R^m$, so that Wasserstein distributionally robust optimization with a type-1 ball is Lipschitz regularization.
--
--   **Formalization Note** The product $\varepsilon \, \mathrm{Lip}(\ell)$ is computed in $[-\infty, +\infty]$ with $0 \cdot \infty = 0$, so at $\varepsilon = 0$ the identity reads $\mathcal R_{0,1}(\widehat{\mathbb P}_N, \ell) = \mathcal R(\widehat{\mathbb P}_N, \ell)$.
--
--   Differences from the source:
--   - reading: ε Lip(ℓ) for ε = 0 and Lip(ℓ) = ∞ → 0 · ∞ = 0 (EReal); reason: the paper allows ε ≥ 0 (p. 6) and Lip(ℓ) = ∞ (p. 9) without defining the product; under this reading the ε = 0 case is the true identity R(P̂N, ℓ) = R(P̂N, ℓ), since the ball of radius 0 is {P̂N}.
--   - encoding: R^m with an arbitrary norm, Ξ = R^m → a finite-dimensional real normed space E, Ξ = Set.univ; reason: same instances up to linear isometry.
--   - encoding: convexity of an extended real-valued ℓ → convexity of the epigraph (`IsConvexExt`); reason: the standard definition for extended real-valued functions.
--   - encoding: E^P[ℓ(ξ)] = ∞ when both parts are infinite (p. 2) → the definition `risk`; reason: the paper's convention written out.
--   - encoding: P(Ξ), all probability distributions on R^m → all Borel probability measures on E (`ambiguityBall` with Ξ = Set.univ); reason: same objects.
--   - encoding: Assumption 1 (p. 9, tacit throughout), measurability (p. 1), N training samples → explicit hypotheses husc, hint, hmeas and 0 < N; reason: the paper's standing assumptions made explicit.
--   - encoding: |ϕ(ξ) − ϕ(ξ′)| undefined when both values are the same infinity → valued ∞ in `lipModulus`; reason: changes no value when ℓ has a finite value, which Assumption 1 guarantees.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Theorem 10, p. 14; Assumption 1, p. 9

import Mathlib
import Definitions.Def_WassersteinDRO_ConvexLossP1_IsConvexExt
import Definitions.Def_WassersteinDRO_ConvexLossP1_empirical
import Definitions.Def_WassersteinDRO_ConvexLossP1_worstCaseRisk
import Definitions.Def_WassersteinDRO_ConvexLossP1_lipModulus

open MeasureTheory

namespace WassersteinDRO.ConvexLossP1

/-- **Theorem 10 (Convex loss and p = 1).**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Theorem 10, p. 14: "Assume that Ξ = R^m and that the loss function ℓ(ξ) is convex. If p = 1 and
P̂N is the empirical distribution, then the worst-case risk (6) coincides with the
Lipschitz-regularized empirical loss, that is, R_{ε,1}(P̂N, ℓ) = R(P̂N, ℓ) + ε Lip(ℓ)."
Standing hypothesis, Assumption 1 (Regularity), p. 9, "tacitly assumed to hold throughout the rest
of the paper": `ℓ` is upper semicontinuous and `∫_{R^m} |ℓ(ξ)| P̂N(dξ) < ∞`. Loss functions are
measurable and extended real-valued (p. 1); `ε ≥ 0` (p. 6); `P̂_N` is (3), p. 2, for `N` samples.

For every `N ≥ 1`, samples `ξ̂_1, …, ξ̂_N ∈ E` (repeats allowed), convex, measurable, upper
semicontinuous `ℓ : E → [−∞, ∞]` with `∫ |ℓ| dP̂_N < ∞`, and `ε ≥ 0`:
`R_{ε,1}(P̂_N, ℓ) = R(P̂_N, ℓ) + ε · Lip(ℓ)`,
where the worst case is over every Borel probability measure `Q` on `E` with `W_1(Q, P̂_N) ≤ ε`.

**Formalization Note.** `(ℝ^m, ‖·‖)` with an arbitrary norm is a finite-dimensional real normed
space `E`; `Ξ = ℝ^m` is `Set.univ`. Convexity is epigraph convexity (`IsConvexExt`). The expectation
convention ("infeasibility trumps unboundedness", p. 2) is built into `risk`. The product `ε · Lip(ℓ)`
is computed in `EReal`, where `0 · ∞ = 0`: at `ε = 0` the identity reads `R_{0,1}(P̂_N, ℓ) = R(P̂_N, ℓ)`
even when `Lip(ℓ) = ∞`; for `ε > 0` and `Lip(ℓ) = ∞` both sides are `+∞`. -/
theorem theorem_10_convex_loss_p_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) (ℓ : E → EReal) (hconv : IsConvexExt ℓ)
    (hmeas : Measurable ℓ) (husc : UpperSemicontinuous ℓ)
    (hint : ∫⁻ ξ, EReal.abs (ℓ ξ) ∂(empirical ξhat) < ⊤) (ε : ℝ) (hε : 0 ≤ ε) :
    worstCaseRisk ε 1 (empirical ξhat) Set.univ ℓ
      = risk (empirical ξhat) ℓ + (ε : EReal) * ((lipModulus ℓ : ENNReal) : EReal) := by sorry

end WassersteinDRO.ConvexLossP1
