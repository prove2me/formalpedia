-- Prove2me | Theorems.Thm_TerracedZonal_Excess_lemma_E_4
-- name    : TerracedZonal.Excess.lemma_E_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:07.886795+00:00
-- url     : https://prove2.me/theorems/582953b4-040b-4001-9160-aedab3b42d97
-- title:
--   Lemma E.4 — unbiased stationary point of $\psi_{\mathrm{stretch}}$
-- statement:
--   Let a terrace have ideal populations $y_k=\bar y+\delta_k$, $k=1,\dots,n$, with $\bar y>0$ and $\sum_k\delta_k=0$, and let $F_\alpha(m)=\sum_k(m-y_k)^2/(y_k^{1-\alpha}m^\alpha)$.
--
--   1. For every $\alpha\in\mathbb R$ and every $r\in(0,1)$ there is a constant $C=C(\alpha,r)$ such that for every such terrace with $|\delta_k|\le r\bar y$ for all $k$, $F_\alpha$ is differentiable at $\bar y$ and
--
--   $$\Big|F_\alpha'(\bar y)-(2-3\alpha)\sum_k\frac{\delta_k^2}{\bar y^2}\Big|\le C\sum_k\frac{|\delta_k|^3}{\bar y^3}.$$
--
--   2. The stationarity condition at the arithmetic mean holds through second order, i.e. $|F_\alpha'(\bar y)|\le C\sum_k|\delta_k|^3/\bar y^3$ with $C=C(\alpha,r)$ uniform as in 1., if and only if $\alpha=2/3$.
--
--   This is why Stage 1 uses the mixed denominator $y^{1/3}m^{2/3}$: the best constant population on a terrace is then the mean ideal population to second order, so the unconstrained dynamic program has no systematic mass drift.
--
--   Differences from the source:
--   - reading: F′_α(ȳ) = (2 − 3α)∑δ_k²/ȳ² + O(∑|δ_k|³/ȳ³) → for each α and each r ∈ (0,1) one constant C(α, r) bounds the remainder for all terraces (any size n ≥ 1, any ȳ > 0) with |δ_k| ≤ rȳ; differentiability at ȳ is asserted; reason: the O(·) is unquantified; the per-ring expansion (28) is uniform for |δ_k/ȳ| ≤ r < 1, so this is the uniform reading the proof gives
--   - reading: the minimizer of F_α equals the arithmetic mean ȳ through second order in δ_k/ȳ iff α = 2/3 → α = 2/3 iff F′_α(ȳ) is bounded by C(α, r)∑|δ_k|³/ȳ³ uniformly as in part 1; reason: the proof identifies the claim with the vanishing of the quadratic term of F′_α(ȳ); the Lean statement asserts that equivalence on all terraces, including the converse for α ≠ 2/3
--   - encoding: a terrace T with index set k ∈ T → n ≥ 1 rings indexed by Fin n; reason: relabelling a finite nonempty index set
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), Lemma E.4, p. 28 (PDF 29)

import Definitions.Def_TerracedZonal_Excess_ContinuumCosts

namespace TerracedZonal.Excess

/-- Lemma E.4, p. 28 (PDF 29). (a) For every `α ∈ ℝ` and every `r ∈ (0,1)` there is a constant
`C`, depending only on `α` and `r`, such that for every terrace of `n ≥ 1` rings with ideal
populations `y_k = ȳ + δ_k`, `ȳ > 0`, `∑ δ_k = 0`, `|δ_k| ≤ r ȳ`, the cost `F_α` is
differentiable at `ȳ` and
`|F_α'(ȳ) - (2 - 3α) ∑ δ_k²/ȳ²| ≤ C ∑ |δ_k|³/ȳ³`.
(b) The derivative at the arithmetic mean vanishes through second order in `δ_k/ȳ`
(i.e. is bounded by a constant times `∑ |δ_k|³/ȳ³`, uniformly as in (a)) if and only if
`α = 2/3`. -/
theorem lemma_E_4 :
    (∀ α r : ℝ, 0 < r → r < 1 → ∃ C : ℝ, ∀ (n : ℕ), 0 < n → ∀ (ybar : ℝ) (δ : Fin n → ℝ),
      0 < ybar → ∑ k, δ k = 0 → (∀ k, |δ k| ≤ r * ybar) →
        DifferentiableAt ℝ (Fcost α (fun k => ybar + δ k)) ybar ∧
        |deriv (Fcost α (fun k => ybar + δ k)) ybar - (2 - 3 * α) * ∑ k, δ k ^ 2 / ybar ^ 2|
          ≤ C * ∑ k, |δ k| ^ 3 / ybar ^ 3) ∧
    (∀ α : ℝ, α = 2 / 3 ↔
      ∀ r : ℝ, 0 < r → r < 1 → ∃ C : ℝ, ∀ (n : ℕ), 0 < n → ∀ (ybar : ℝ) (δ : Fin n → ℝ),
        0 < ybar → ∑ k, δ k = 0 → (∀ k, |δ k| ≤ r * ybar) →
          |deriv (Fcost α (fun k => ybar + δ k)) ybar| ≤ C * ∑ k, |δ k| ^ 3 / ybar ^ 3) := by sorry

end TerracedZonal.Excess
