-- Prove2me | Theorems.Thm_PolyVoting_theorem_3_i
-- name    : PolyVoting.theorem_3_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:24.810836+00:00
-- url     : https://prove2.me/theorems/98be3bae-c301-471b-a713-e4161556bbca
-- title:
--   Theorem 3 (i), (2.9) — lower-tail large deviations of the volume $N_t$
-- statement:
--   Let $f_\alpha(\lambda)=(1+\alpha)\lambda\log\lambda-(1+\alpha)\lambda+\lambda^{-\alpha}$ on $(0,\infty)$, and let $\lambda_-(\alpha)$ be its smaller root. For each $0<\lambda<\lambda_-(\alpha)$ and any $\varepsilon>0$, for all large $t$,
--   $$\mathbb P\big(N_t<\lambda t^{\frac1{1+\alpha}}\big)\le\exp\Big(-(1-\varepsilon)f_\alpha(\lambda)\,t^{\frac1{1+\alpha}}\Big).$$
--
--   The bound is what lets the proof of (2.16) discard the event that few stakes have been awarded by time $t$.
--
--   **Formalization Note** The condition $\lambda<\lambda_-(\alpha)$ is written as: $f_\alpha>0$ on $(0,\lambda]$. For $\alpha>0$, $f_\alpha$ is strictly convex on $(0,\infty)$, tends to $+\infty$ at $0^+$ and has $f_\alpha(1)=-\alpha<0$, so it has exactly two roots and the two conditions coincide.
--
--   Differences from the source:
--   - encoding: the Poly(α) rule described by (2.3)–(2.6), K ∈ ℕ₊ bidders, stakes n_{k,t} → `Model μ K α n₀`: the joint conditional one-step law, stakes in Fin K → ℕ, real α ≥ 0 with Real.rpow, and 1 ≤ N; reason: the conditional one-step law and n₀ determine the law of the chain; 1 ≤ N only keeps N_t^{−α} defined
--   - encoding: each λ < λ₋(α), the smaller root → 0 < λ and f_α > 0 on (0, λ]; reason: for α > 0, f_α is strictly convex, → +∞ at 0⁺ and f_α(1) = −α < 0, so the two conditions coincide; no undefined root appears
--   - reading: "the two roots of f_α(·) on (−∞, ∞)" → roots in (0, ∞); reason: f_α is defined on (0, ∞) only
--   - generalization: two roots λ₋(α) < λ₊(α), which exist for α > 0 → α ≥ 0 with the same root-free hypothesis (λ < 1 at α = 0); reason: at α = 0, N_t = N + t and the bound is trivial; the statement specializes to the source for α > 0
--   - encoding: "as t → ∞" → for all large t, the threshold depending on α, λ, ε, n₀; reason: that is the meaning of an asymptotic upper bound
-- source:
--   Tang & Yao, Polynomial Voting Rules, arXiv:2206.10105v5, Theorem 3 (i), display (2.9), p.7

import Mathlib
import Definitions.Def_PolyVoting_Model
import Definitions.Def_PolyVoting_fAlpha

open MeasureTheory Filter

namespace PolyVoting

/-- **Theorem 3 (i), display (2.9)** (Tang & Yao, *Polynomial Voting Rules*, arXiv:2206.10105v5, p.7):
the lower-tail large-deviation bound for the volume.

**Formalization Note.** The paper takes `λ < λ₋(α)`, the smaller of the two roots of `f_α`. The
hypothesis `hroot` says that `f_α` has no zero and is positive on `(0, λ]`. For `α > 0`, `f_α` is
strictly convex on `(0, ∞)`, tends to `+∞` at `0⁺`, and `f_α(1) = -α < 0`, so `hroot` is exactly
`0 < λ < λ₋(α)`. For `α = 0` the two roots do not exist, `hroot` says `λ < 1`, and the statement is
an extension. "As `t → ∞`" means for all large `t`, the threshold depending on the other data. -/
theorem theorem_3_i {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℕ} {α : ℝ} {n₀ : Fin K → ℕ} (M : Model μ K α n₀)
    {lam : ℝ} (hlam : 0 < lam) (hroot : ∀ x ∈ Set.Ioc 0 lam, 0 < fAlpha α x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, μ {ω | (M.total t ω : ℝ) < lam * (t : ℝ) ^ (1 / (1 + α))} ≤
      ENNReal.ofReal (Real.exp (-(1 - ε) * fAlpha α lam * (t : ℝ) ^ (1 / (1 + α)))) := by sorry

end PolyVoting
