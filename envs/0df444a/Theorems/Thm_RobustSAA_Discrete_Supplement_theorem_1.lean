-- Prove2me | Theorems.Thm_RobustSAA_Discrete_Supplement_theorem_1
-- name    : RobustSAA.Discrete.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:41:22.467182+00:00
-- url     : https://prove2.me/theorems/bc14bec0-8046-4b46-916b-b50b417ee8db
-- title:
--   Theorem 1 (corrected: coercive branch needs an integrable minorant) — the robust problem has a finite, attained optimum
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ and $X\subseteq\mathbb R^{d_x}$ be closed, let $c(x;\xi)$ be a cost, measurable in $\xi$ for every $x$, and let $\mathcal F$ be a nonempty set of probability laws on $\Xi$. Write $C(x;\mathcal F)=\sup_{F_0\in\mathcal F}\mathbb E_{F_0}[c(x;\xi)]$ and $\bar z=\inf_{x\in X}C(x;\mathcal F)$, the optimal value of (3). Suppose that $C(x_0;\mathcal F)<\infty$ for some $x_0\in X$ and that the family $\{c(\cdot;\xi):\xi\in\Xi\}$ is equicontinuous on $\mathbb R^{d_x}$ (Definition 1). Then:
--
--   1. If $X$ is compact, $\bar z$ is finite and $\bar z=C(\bar x;\mathcal F)$ for some $\bar x\in X$.
--   2. If $\lim_{\|x\|\to\infty}c(x;\xi)=\infty$ for every $\xi\in\Xi$, and in addition some $F_0\in\mathcal F$ admits an $F_0$-integrable $g$ with $g(\xi)\le c(x;\xi)$ for all $x\in X$ and $\xi\in\Xi$, then $\bar z$ is finite and attained at some $\bar x\in X$.
--
--   $$-\infty<\bar z=\min_{x\in X}C(x;\mathcal F)<\infty.$$
--
--   The result is the Weierstrass-type existence theorem behind every robust SAA problem of the paper; Theorems 8, 11, 12 and 14 assume its hypotheses.
--
--   Differences from the source:
--   - reading: C(x;𝓕) for a data-driven uncertainty set 𝓕 → any nonempty set 𝓕 of laws on Ξ; reason: for 𝓕 = ∅ the supremum is −∞ and z̄ is not finite; the source's DUSs are nonempty
--   - encoding: E_{F₀}[c(x;ξ)] for any law → the integral when c(x;·) is F₀-integrable and +∞ otherwise (the published RobustSAA.Convergence.expect convention); reason: series convention; a member under which the cost is not integrable never lowers a worst case
--   - reading: a cost whose expectations E_{F₀}[c(x;ξ)] are taken → c(x;·) is measurable for every x; reason: expectations of c(x;·) presuppose measurability; standing convention of the field
--   - correction: if lim_{‖x‖→∞} c(x;ξ) = ∞ for all ξ, then z̄ is finite and achieved → this branch additionally assumes some F₀ ∈ 𝓕 and an F₀-integrable g with g(ξ) ≤ c(x;ξ) for all x ∈ X, ξ ∈ Ξ; reason: counterexample in DISPROOF.md: Ξ = {1,2,…}, F(ξ = k) = 2^{−k}, 𝓕 = {F}, X = ℝ, c(x;ξ) = |x| − 2ξ·2^ξ·max(0, 1 − |x − ξ|) satisfies every printed hypothesis but C(x;𝓕) = −x for x ≥ 0, so z̄ = −∞; §10.1 applies monotone convergence to inf_{j≥i} c(x_j;ξ), which needs exactly such a minorant; excluded: coercive costs without an integrable lower envelope under any member of 𝓕
--   - encoding: z̄ of (3) is finite and achieved at x̄ ∈ X → ⨅_{x∈X} C(x;𝓕) ∉ {−∞, +∞} and equals C(x̄;𝓕) for some x̄ ∈ X; reason: extended-real infimum; same instances
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 1, p. 5 (proof §10.1, p. 33)

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting

namespace RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Convergence

theorem theorem_1 {d dx : ℕ} (Ξ : Set (Pt d)) (hΞ : IsClosed Ξ) (X : Set (Pt dx))
    (hX : IsClosed X) (c : Pt dx → ↥Ξ → ℝ) (hmeas : ∀ x, Measurable (c x))
    (𝓕 : Set (ProbabilityMeasure ↥Ξ)) (h𝓕 : 𝓕.Nonempty)
    (hx₀ : ∃ x₀ ∈ X, worstCase 𝓕 (c x₀) < ⊤) (hequi : Assumption1 X c) :
    (IsCompact X →
      ∃ xbar ∈ X, worstCase 𝓕 (c xbar) = ⨅ x ∈ X, worstCase 𝓕 (c x) ∧
        (⨅ x ∈ X, worstCase 𝓕 (c x)) ≠ ⊤ ∧ (⨅ x ∈ X, worstCase 𝓕 (c x)) ≠ ⊥) ∧
    ((∀ ξ : ↥Ξ, Tendsto (fun x => c x ξ) (Bornology.cobounded (Pt dx)) atTop) →
      (∃ F₀ ∈ 𝓕, ∃ g : ↥Ξ → ℝ, Integrable g (F₀ : Measure ↥Ξ) ∧ ∀ x ∈ X, ∀ ξ, g ξ ≤ c x ξ) →
      ∃ xbar ∈ X, worstCase 𝓕 (c xbar) = ⨅ x ∈ X, worstCase 𝓕 (c x) ∧
        (⨅ x ∈ X, worstCase 𝓕 (c x)) ≠ ⊤ ∧ (⨅ x ∈ X, worstCase 𝓕 (c x)) ≠ ⊥) := by sorry

end RobustSAA.Discrete.Supplement
