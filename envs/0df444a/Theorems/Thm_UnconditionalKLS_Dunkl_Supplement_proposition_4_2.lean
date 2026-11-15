-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_Supplement_proposition_4_2
-- name    : UnconditionalKLS.Dunkl.Supplement.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:17:33.310685+00:00
-- url     : https://prove2.me/theorems/8c6a6b76-1397-4c33-899c-ea94f708b43d
-- title:
--   Proposition 4.2 — convexifying coordinatewise contraction: $\nu=(T^{-1})_\#\eta$ log-concave and $C_P(\eta)\le C_P(\nu)\le\max_j\mathbb E_\eta[1/r(h^{-1}(X_j))]$
-- statement:
--   Let $\mathbb R^n_+=(0,\infty)^n$ and let $\eta$ be the probability measure on $\mathbb R^n_+$ with density proportional to $e^{-V}$, where $V\in C^2(\mathbb R^n_+)$ is convex and $\partial_jV\ge0$ on $\mathbb R^n_+$ for every $1\le j\le n$. Let $h:(0,\infty)\to(0,\infty)$ be an increasing $C^3$ bijection such that, for every $t>0$,
--
--   $$0<h'(t)\le1,\qquad h''(t)\ge0,\qquad r(t):=-(\log h')''(t)>0.$$
--
--   Let $T(y)=(h(y_1),\dots,h(y_n))$ and $\nu=(T^{-1})_\#\eta$, where $T^{-1}(x)=(h^{-1}(x_1),\dots,h^{-1}(x_n))$. Then all three of the following hold:
--
--   1. $\nu$ is log-concave, i.e. it has a density $e^{-U}$ with $U:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ convex;
--   2. $C_P(\eta)\le C_P(\nu)$;
--   3. $$C_P(\nu)\le\max_{j\in[n]}\mathbb E_\eta\Big[\frac{1}{r(h^{-1}(X_j))}\Big],$$ where $X\sim\eta$ and the right side may be $+\infty$.
--
--   The proposition realizes $\eta$ as a $1$-Lipschitz image of a measure whose potential is uniformly convex in an averaged sense, so that the improved Brascamp–Lieb inequality (Proposition 1.2) applies. Corollary 4.3 is the case $h(t)=\sqrt{1+t^2}-1$.
--
--   **Formalization Note** $h$ is a function on $\mathbb R$ whose values off $(0,\infty)$ are irrelevant; its regularity, bijectivity, monotonicity and (4.8) are required on $(0,\infty)$ only. $h^{-1}$ is the inverse of $h$ on $(0,\infty)$. Expectations are $[0,\infty]$-valued lower integrals.
--
--   Differences from the source:
--   - encoding: η a probability measure on ℝⁿ₊ with density proportional to e^{-V}, V ∈ C²(ℝⁿ₊) → V : ℝⁿ → ℝ, C² and convex on the open orthant, η = Z_V⁻¹·1_{ℝⁿ₊}e^{-V}dx with the hypothesis Z_V ≠ ∞; reason: "probability measure with density proportional to" needs a finite normalizer; Z_V > 0 is automatic; values of V off the orthant are irrelevant
--   - encoding: h : (0, ∞) → (0, ∞) an increasing C³ bijection with (4.8) for t > 0 → h : ℝ → ℝ with ContDiffOn ℝ 3 on (0, ∞), MonotoneOn and BijOn h (0, ∞) (0, ∞), and (4.8) via deriv for every t > 0; reason: only the restriction to (0, ∞) enters; on an open set deriv is the classical derivative
--   - encoding: T^{-1} → x ↦ (h⁻¹(x_j))_j with h⁻¹ = Function.invFunOn h (0, ∞); reason: agrees with the inverse of T on ℝⁿ₊, which carries η, and is constant off it, hence measurable
--   - encoding: ν is log-concave → LogConcaveLaw ν: ν = e^{-U} dx with U : ℝⁿ → WithTop ℝ of convex epigraph, e^{-∞} = 0; reason: the paper's p. 1 definition without the unconditionality, which ν does not have
--   - encoding: max_{j∈[n]} 𝔼_η[1/r(h^{-1}(X_j))] → ⨆ over j : Fin n of ∫⁻ ofReal(1/r(h⁻¹(x_j))) dη in ℝ≥0∞; reason: the integrand is positive η-a.e.; a divergent expectation is +∞, as in the proof ("If the right-hand side of (4.9) is infinite, there is nothing to prove")
--   - encoding: ∂_jV ≥ 0 → the base Fréchet partial d V j x ≥ 0 for x ∈ ℝⁿ₊; reason: V is differentiable on the open orthant, so this is the classical partial
--   - encoding: C_P(·), the best constant in (1.1) → the base `poincare` in ℝ≥0∞ (ambient locally Lipschitz tests on ℝⁿ, +∞ if no finite constant works); reason: same value whenever the constant is finite; +∞ otherwise
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 30, Proposition 4.2, (4.8)–(4.9); proof p. 30. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Supplement_Model

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl.Supplement
open UnconditionalKLS.Dunkl
/-- Proposition 4.2, p. 30 (convexifying coordinatewise contraction, (4.8)–(4.9)). -/
theorem proposition_4_2 {n : ℕ} (V : Fn n) (hV : ContDiffOn ℝ 2 V posOrthant)
    (hV_convex : ConvexOn ℝ posOrthant V)
    (hV_mono : ∀ j : Fin n, ∀ x ∈ posOrthant, 0 ≤ d V j x)
    (hZ : orthantNormalizer V ≠ ⊤)
    (h : ℝ → ℝ) (hh : ContDiffOn ℝ 3 h (Set.Ioi 0)) (hh_mono : MonotoneOn h (Set.Ioi 0))
    (hh_bij : Set.BijOn h (Set.Ioi 0) (Set.Ioi 0))
    (h48 : ∀ t : ℝ, 0 < t →
      0 < deriv h t ∧ deriv h t ≤ 1 ∧ 0 ≤ deriv (deriv h) t ∧ 0 < rate h t) :
    LogConcaveLaw (pullbackLaw h (orthantLaw V)) ∧
    poincare (orthantLaw V) ≤ poincare (pullbackLaw h (orthantLaw V)) ∧
    poincare (pullbackLaw h (orthantLaw V)) ≤
      ⨆ j : Fin n, ∫⁻ x, ENNReal.ofReal (1 / rate h (hInv h (x j))) ∂orthantLaw V := by sorry
end UnconditionalKLS.Dunkl.Supplement
