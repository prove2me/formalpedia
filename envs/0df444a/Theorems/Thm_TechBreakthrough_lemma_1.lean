-- Prove2me | Theorems.Thm_TechBreakthrough_lemma_1
-- name    : TechBreakthrough.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:08.10264+00:00
-- url     : https://prove2.me/theorems/af535980-6166-4381-aaa5-918c0bc60e9b
-- title:
--   (17), smooth fit and Lemma 1 — the stand-alone problem (corrected: x_R exists iff R > 0 somewhere)
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`).
--
--   A threshold exists if and only if $R(x)>0$ for some $x\in\mathcal I$. For every threshold $x_R$: $x_R>x_0$ for every $x_0$ as in A3; for every fundamental pair,
--
--   $$V_R(x)=\begin{cases}\dfrac{h_1(x)}{h_1(x_R)}R(x_R)&x<x_R,\\[1ex] R(x)&x\ge x_R,\end{cases}\qquad R'(x_R)=\frac{h_1'(x_R)}{h_1(x_R)}R(x_R);$$
--
--   and $V_R>0$ on $\mathcal I$ and $R>0$ on $[x_R,\beta)$.
--
--   The threshold $x_R$ enters every statement that follows.
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - correction: A3 guarantees that the optimal stopping region is of the form [x_R, β) (p.11) → the threshold exists if and only if R > 0 somewhere, and every other clause is stated for every threshold; reason: false as printed: geometric Brownian motion dX = √2 X dW, r = 2, R(x) = −x²/(1 + x⁶), G(x) = √x, f(y) = e^{−y} satisfies A1–A8 with V_R ≡ 0 and {V_R = R} = ∅; such an x_R exists exactly when R > 0 somewhere (lemma_1)
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, (17) and Lemma 1, p.11; proof of Lemma 1, p.40

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_E

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- The stand-alone problem (10): the threshold, (17), smooth fit and Lemma 1,
arXiv:2106.05112v1, p.11 (proof of Lemma 1, p.40).

**Correction.** The page says that A3 guarantees `{V_R = R} = [x_R, β)`. That is false without
`∃ x ∈ 𝓘, R(x) > 0`: for geometric Brownian motion with `r = 2` and `R(x) = −x²/(1 + x⁶)`,
`V_R ≡ 0 > R`. The first clause here says that such a threshold exists exactly when `R` is positive
somewhere. The remaining clauses are the page's, for every threshold `x_R`: `x_R > x₀`, (17) and
smooth fit for every fundamental pair, `V_R > 0` on `𝓘`, `R > 0` on `[x_R, β)`. -/
theorem lemma_1 (M : Model) (hM : M.Valid) :
    ((∃ x ∈ M.I, 0 < M.R x) ↔ ∃ xR, M.IsThreshold xR) ∧
    ∀ xR, M.IsThreshold xR →
      (∀ x₀ ∈ M.I, (∀ x ∈ M.I, x < x₀ → 0 < M.gap x) → (∀ x ∈ M.I, x₀ < x → M.gap x < 0) →
        x₀ < xR) ∧
      (∀ h₁ h₂, M.IsFundamentalPair h₁ h₂ →
        (∀ x ∈ M.I, M.VR x = if x < xR then h₁ x / h₁ xR * M.R xR else M.R x) ∧
        deriv M.R xR = deriv h₁ xR / h₁ xR * M.R xR) ∧
      (∀ x ∈ M.I, 0 < M.VR x) ∧
      ∀ x ∈ M.fromLevel xR, 0 < M.R x := by sorry

end TechBreakthrough
