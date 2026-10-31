-- Prove2me | Theorems.Thm_RobustRiskOpt_var_perturbation_ge
-- name    : RobustRiskOpt.var_perturbation_ge
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:51.241517+00:00
-- url     : https://prove2.me/theorems/afc657cf-5e59-4f3a-b83d-f197e9b0646e
-- title:
--   p.30 — $\mathrm{VaR}_p$ of the optimized position jumps under perturbation
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $n\ge1$, $p\in(0,1)$, and let $X$ be an $n$-dimensional random vector with law $\mu_X$. Let $v:\mathbb R^n\to\mathbb R\cup\{-\infty\}$ and $w:\mathbb R^n\to\mathbb R$ be measurable, let $\gamma:\mathbb R^n\to(0,\infty)$ be measurable, let $x_0\in\mathbb R$, and let $\mathcal G$ be the admissible set (7). Suppose that Assumptions G and V hold for $\rho=\mathrm{VaR}_p$.
--
--   Let $g_X\in\mathcal G_X(\rho)$ be an optimizer. Let $a^+$ be a real number with $\mathrm{VaR}_p(g_X(X))<a^+\le\mathrm{VaR}_q(g_X(X))$ for all $q\in(p,1)$. Then for every $\varepsilon>0$ there is a random vector $Z$ with $|Z(\omega)-X(\omega)|\le\varepsilon$ for all $\omega$ and
--
--   $$
--   \mathrm{VaR}_p(g_X(Z))\ge a^+>\mathrm{VaR}_p(g_X(X)).
--   $$
--
--   So an arbitrarily small perturbation of the model moves the value of the fixed position across the jump, which shows that $Z\mapsto\rho(g_X(Z))$ is not $\pi$-continuous at $X$.
--
--   Differences from the source:
--   - reading: the budget E[g(X)γ(X)] ⩾ x0 of (7), for which the paper does not say what happens when γg is not integrable → budget is the extended-value expectation E[(γg)₊] − E[(γg)₋] in EReal: the value +∞ is feasible and an undefined difference is ⊥, hence infeasible; reason: the function ĝ = g_X 1_{Aᶜ} + w 1_A of the proof, p.29, must stay in 𝒢 and need not be integrable, since Assumption G does not bound E[γ(X)|w(X)|]; an integrable-only reading breaks that step
--   - generalization: the probability space (Ω, F, P) is atomless (§2.1, p.5) → no atomlessness hypothesis on Ω; reason: it follows from the density of X in Assumption G, so the printed setting is a special case
--   - generalization: γ is bounded from above (Assumption V) → γ is bounded above μ_X-almost everywhere; reason: the printed pointwise bound implies it; the proof takes all inequalities μ_X-a.s. (p.28)
--   - generalization: the proof normalizes E[γ(X)] = 1 (p.28) → no normalization of γ; reason: the normalized case is a special case, and rescaling γ does not change the problem
--   - encoding: μ_X has a positive density on its support, which is a convex subset of ℝⁿ → μ_X and Lebesgue measure restricted to a convex set S are mutually absolutely continuous; reason: the density is positive a.e. on S and zero a.e. off S; a convex set and its closure differ by a null set, so the instances are the same
--   - encoding: v has values in ℝ ∪ {−∞} → v has values in EReal; reason: the value +∞ is excluded by 𝒢 ≠ ∅, since v ⩽ g < +∞ pointwise
--   - encoding: ρ(g(X)) and ρ(X; 𝒢) are extended real numbers → they are EReal-valued, VaR_p being the cast of the real VaR and the infimum being taken in EReal; reason: same values; a real infimum over 𝒢 could be a junk value
--   - encoding: ℝⁿ with the Euclidean norm, n a positive integer → EuclideanSpace ℝ (Fin n) with 0 < n; reason: same space and norm
--   - reading: the perturbation Z_ε is built from the printed nearest-point map f_ε → a measurable Z with displacement at most ε exists; reason: a Borel set need not have nearest points; see the item exists_perturbation
--   - generalization: VaR_p(g_X(Z_ε)) ⩾ lim_{q↓p} VaR_q(g_X(X)) → the bound holds for every level a⁺ strictly above VaR_p and below every VaR_q; reason: the right limit is such a level
-- source:
--   Embrechts–Schied–Wang, Robustness in the Optimization of Risk Measures, arXiv:1809.09268v3, 11 Feb 2021, proof of Theorem 1, p.30

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting
import Definitions.Def_RobustRiskOpt_Admissible
import Definitions.Def_RobustRiskOpt_Assumptions

open MeasureTheory

namespace RobustRiskOpt

open ESAxioms.Characterization

/-- p.30, in the proof of Theorem 1 (Embrechts–Schied–Wang, arXiv:1809.09268v3): for an optimizer
`g_X` and a level `a⁺` as in `quantile_jump`, every `ε > 0` admits a measurable `ε`-perturbation
`Z` of `X` with `VaR_p(g_X(Z)) ≥ a⁺ > VaR_p(g_X(X))`, which is the discontinuity of
`Z ↦ ρ(g_X(Z))` at `X`. -/
theorem var_perturbation_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (hn : 0 < n) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (X : Ω → E n) (hX : Measurable X)
    (v : E n → EReal) (w γ : E n → ℝ) (x₀ : ℝ) (hv : Measurable v) (hw : Measurable w)
    (hγ : Measurable γ) (hγpos : ∀ x, 0 < γ x) (hG : AssumptionG P X v w γ x₀)
    (hV : AssumptionV P p X v w γ x₀)
    (g : E n → ℝ)
    (hg : g ∈ optimizers (varObj P p) X (admissible P X v w γ x₀))
    (aPlus : ℝ) (ha : VaR P p (g ∘ X) < aPlus) (ha' : ∀ q ∈ Set.Ioo p 1, aPlus ≤ VaR P q (g ∘ X))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : Ω → E n, Measurable Z ∧ (∀ ω, ‖Z ω - X ω‖ ≤ ε) ∧ aPlus ≤ VaR P p (g ∘ Z) := by sorry

end RobustRiskOpt
