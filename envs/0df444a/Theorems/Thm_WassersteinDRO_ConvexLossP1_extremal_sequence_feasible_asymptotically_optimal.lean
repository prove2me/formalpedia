-- Prove2me | Theorems.Thm_WassersteinDRO_ConvexLossP1_extremal_sequence_feasible_asymptotically_optimal
-- name    : WassersteinDRO.ConvexLossP1.extremal_sequence_feasible_asymptotically_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:54:43.57206+00:00
-- url     : https://prove2.me/theorems/40727a2b-a0c5-498a-b896-a199f9d9ef17
-- title:
--   The sequence $\mathbb Q_n$ is feasible and asymptotically optimal in (6)
-- statement:
--   Let $(E, \|\cdot\|)$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra and dual norm $\|\cdot\|_*$. Let $N \ge 1$, let $\widehat\xi_1, \dots, \widehat\xi_N \in E$ with empirical distribution $\widehat{\mathbb P}_N$, and let $\ell : E \to [-\infty, +\infty]$ be convex, measurable and upper semicontinuous with $\int |\ell| \, \mathrm d\widehat{\mathbb P}_N < \infty$. Let $\varepsilon \ge 0$, $i_0 \in \{1, \dots, N\}$ and $\xi^\star \in E$ with $\|\xi^\star\| \le 1$, and let $\mathbb Q_n$ be the distributions
--   $$\mathbb Q_n = \frac1N \sum_{i \ne i_0} \delta_{\widehat\xi_i} + \frac{n-1}{nN} \, \delta_{\widehat\xi_{i_0}} + \frac{1}{nN} \, \delta_{\widehat\xi_{i_0} + \varepsilon n N \xi^\star}.$$
--   Then, with $\Xi = E$ and $p = 1$:
--
--   1. (feasibility) $\mathbb Q_n \in \mathbb B_{\varepsilon,1}(\widehat{\mathbb P}_N)$ for every $n \ge 1$;
--   2. (lower bound) for every $z \in E^*$ with $\ell^*(z) < \infty$,
--   $$\mathcal R(\widehat{\mathbb P}_N, \ell) + \varepsilon \, z(\xi^\star) \le \liminf_{n \to \infty} \mathcal R(\mathbb Q_n, \ell);$$
--   3. (asymptotic optimality) if $z^\star$ is a maximizer of problem (13), i.e. $\ell^*(z^\star) < \infty$ and $\|z\|_* \le \|z^\star\|_*$ whenever $\ell^*(z) < \infty$, and $\xi^\star \in \arg\max_{\|\xi\| \le 1} z^\star(\xi)$, then
--   $$\lim_{n \to \infty} \mathcal R(\mathbb Q_n, \ell) = \mathcal R_{\varepsilon,1}(\widehat{\mathbb P}_N, \ell).$$
--
--   The sequence shows that the worst case in Theorem 10 is approached by pushing a vanishing amount of probability mass to infinity along the direction $\xi^\star$.
--
--   Differences from the source:
--   - generalization: the lower bound only along a maximizer z⋆ of (13), whose existence the paper assumes → clause 2, for every z with ℓ∗(z) < ∞ and every ξ⋆ in the closed unit ball, with no maximizer required; reason: an additional true clause; clauses 1 and 3 are the paper's sentence unchanged.
--   - reading: "feasible … as n ≥ 1" → Q_n ∈ B_{ε,1}(P̂N) for every n ≥ 1; reason: the paper's range of n.
--   - reading: "asymptotically optimal in (6) as n tends to infinity" → R(Q_n, ℓ) converges to the supremum (6) in [−∞, ∞]; reason: the meaning of an asymptotically optimal sequence for a supremum.
--   - encoding: z⋆ a maximizer of (13) and ξ⋆ ∈ arg max_{‖ξ‖≤1} ξ^⊤z⋆ → ℓ∗(z⋆) < ∞ ∧ ∀ z, ℓ∗(z) < ∞ → ‖z‖ ≤ ‖z⋆‖, and ‖ξ⋆‖ ≤ 1 ∧ ∀ ξ, ‖ξ‖ ≤ 1 → z⋆(ξ) ≤ z⋆(ξ⋆); reason: the definitions of the two argmax sets written out.
--   - encoding: the conditions of Theorem 10 and Assumption 1 (p. 9) → explicit hypotheses: Ξ = E, p = 1, ℓ convex (epigraph), measurable, upper semicontinuous, ∫|ℓ| dP̂N < ∞, N ≥ 1, ε ≥ 0; reason: the paper's standing assumptions made explicit.
--   - encoding: R^m with an arbitrary norm, z ∈ R^m → a finite-dimensional real normed space E, z a continuous linear functional with its operator norm; reason: same instances up to linear isometry.
--   - encoding: E^P[ℓ(ξ)] = ∞ when both parts are infinite (p. 2) → the definition `risk`; reason: the paper's convention written out.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §2.2, unnumbered paragraph after Remark 3, p. 14

import Mathlib
import Definitions.Def_WassersteinDRO_ConvexLossP1_IsConvexExt
import Definitions.Def_WassersteinDRO_ConvexLossP1_empirical
import Definitions.Def_WassersteinDRO_ConvexLossP1_worstCaseRisk
import Definitions.Def_WassersteinDRO_ConvexLossP1_conjugate
import Definitions.Def_WassersteinDRO_ConvexLossP1_extremalSeq

open MeasureTheory Filter Topology

namespace WassersteinDRO.ConvexLossP1

/-- **The sequence `Q_n` is feasible and asymptotically optimal in (6).**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §2.2, unnumbered paragraph after Remark 3, p. 14: "To do so, choose a maximizer z⋆ of problem
(13), which is generally intractable as pointed out in Remark 3. Moreover, select i0 ∈ [N] and
ξ⋆ ∈ arg max_{‖ξ‖≤1} ξ^⊤z⋆. Then, the distributions
Q_n = (1/N) Σ_{i≠i0}^{N} δ_{ξ̂i} + (n − 1)/(nN) δ_{ξ̂i0} + 1/(nN) δ_{ξ̂i0+εnNξ⋆}
can be shown to be feasible and asymptotically optimal in (6) as n ≥ 1 tends to infinity."
Setting: "the conditions of Theorem 10" (p. 14): `Ξ = ℝ^m`, `p = 1`, `ℓ` convex, `P̂_N` the
empirical distribution; Assumption 1 (p. 9): `ℓ` upper semicontinuous and `∫ |ℓ| dP̂_N < ∞`;
`ℓ` measurable (p. 1); `ε ≥ 0` (p. 6).

Let `N ≥ 1`, samples `ξ̂_1, …, ξ̂_N ∈ E`, `ℓ : E → [−∞, ∞]` convex, measurable, upper
semicontinuous with `∫ |ℓ| dP̂_N < ∞`, `ε ≥ 0`, `i0` an index and `ξ⋆ ∈ E` with `‖ξ⋆‖ ≤ 1`. Then
1. (feasibility) `Q_n ∈ B_{ε,1}(P̂_N)` (with `Ξ = E`) for every `n ≥ 1`;
2. (lower bound) for every `z ∈ E*` with `ℓ*(z) < ∞`,
   `R(P̂_N, ℓ) + ε z(ξ⋆) ≤ liminf_{n→∞} R(Q_n, ℓ)`;
3. (asymptotic optimality) if `z⋆` maximizes `‖z‖∗` over `{z : ℓ*(z) < ∞}` and `ξ⋆` maximizes
   `ξ ↦ z⋆(ξ)` over the closed unit ball, then `R(Q_n, ℓ) → R_{ε,1}(P̂_N, ℓ)` as `n → ∞`.

**Formalization Note.** Clauses 1 and 3 are the paper's sentence. Clause 2 holds for every `z` in
the domain of `ℓ*` and every `ξ⋆` in the unit ball, and does not need a maximizer `z⋆` of (13),
which the paper tacitly assumes to exist. "Asymptotically optimal" is read as convergence of the
risks `R(Q_n, ℓ)` to the supremum (6), in `[−∞, ∞]`. -/
theorem extremal_sequence_feasible_asymptotically_optimal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) (ℓ : E → EReal) (hconv : IsConvexExt ℓ)
    (hmeas : Measurable ℓ) (husc : UpperSemicontinuous ℓ)
    (hint : ∫⁻ ξ, EReal.abs (ℓ ξ) ∂(empirical ξhat) < ⊤) {ε : ℝ} (hε : 0 ≤ ε) (i0 : Fin N)
    (ξstar : E) (hξstar : ‖ξstar‖ ≤ 1) :
    (∀ n : ℕ, 1 ≤ n →
        extremalSeq ξhat i0 ξstar ε n ∈ ambiguityBall ε 1 (empirical ξhat) Set.univ) ∧
      (∀ z : StrongDual ℝ E, conjugate ℓ z < ⊤ →
        risk (empirical ξhat) ℓ + ((ε * z ξstar : ℝ) : EReal) ≤
          liminf (fun n : ℕ => risk (extremalSeq ξhat i0 ξstar ε n) ℓ) atTop) ∧
      (∀ zstar : StrongDual ℝ E, conjugate ℓ zstar < ⊤ →
        (∀ z : StrongDual ℝ E, conjugate ℓ z < ⊤ → ‖z‖ ≤ ‖zstar‖) →
        (∀ ξ : E, ‖ξ‖ ≤ 1 → zstar ξ ≤ zstar ξstar) →
        Tendsto (fun n : ℕ => risk (extremalSeq ξhat i0 ξstar ε n) ℓ) atTop
          (𝓝 (worstCaseRisk ε 1 (empirical ξhat) Set.univ ℓ))) := by sorry

end WassersteinDRO.ConvexLossP1
