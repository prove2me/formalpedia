-- Prove2me | Theorems.Thm_TrustIPM_lemma_4
-- name    : TrustIPM.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:17.864741+00:00
-- url     : https://prove2.me/theorems/a4447294-0cf0-4bea-ba89-bad7fd93e85c
-- title:
--   Lemma 4 — $g(\theta)/g(0)\in[3/4,4/3]$ and a bound on $\theta^3|(\log g)'''(\theta)|$
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ have $L_1$-Lipschitz first derivatives and $L_2$-Lipschitz second derivatives on $[0,\theta]$, where $\theta\ge0$ and $L_1,L_2\in(0,\infty)$. Assume $g(0)>0$, $\beta\in(0,1/4]$ and
--
--   $$
--   \frac{|\theta g'(0)|}{g(0)}+\frac{L_1\theta^2}{g(0)}\le\beta .
--   $$
--
--   Then
--
--   1. $g(\theta)/g(0)\in[3/4,\,4/3]$, and
--   2. $$\theta^3\Bigl|\frac{\partial^3\log g(\theta)}{\partial\theta^3}\Bigr|\le\frac{2L_2\theta^3+8L_1\theta^2\beta}{g(0)}+5\beta^3 .$$
--
--   The log barrier is not globally smooth; this lemma bounds the local Lipschitz constant of the second derivative of $\log g$ for $g(\theta)=a_i(x+\theta v)$, which feeds Lemma 5.
--
--   **Formalization Note** $g$, $g'$ and $g''$ are assumed differentiable at every point of $[0,\theta]$; the third derivative of $\log g$ at $\theta$ is `iteratedDeriv 3 (fun t => Real.log (g t)) θ`.
--
--   Differences from the source:
--   - reading: g has L₁-Lipschitz first and L₂-Lipschitz second derivatives on [0, θ] (existence of g′, g″, g‴ implicit) → g, g′, g″ differentiable at every point of [0, θ], plus the two Lipschitz conditions; reason: the derivatives in the hypothesis and in the conclusion must exist; continuity of g‴ is not assumed
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Lemma 4, p.8

import Mathlib
import Definitions.Def_TrustIPM_HasLipDerivOn

namespace TrustIPM

/-- **Lemma 4** (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems with
nonconvex constraints*, arXiv:1807.00404v5, Lemma 4, p.8). Suppose `g : ℝ → ℝ` has `L₁`-Lipschitz
first derivatives and `L₂`-Lipschitz second derivatives on `[0, θ]`, `θ ∈ ℝ₊`. Further assume
`g(0) > 0`, `β ∈ (0, 1/4]`, and `|θg′(0)|/g(0) + L₁θ²/g(0) ≤ β`. Then `g(θ)/g(0) ∈ [3/4, 4/3]` and
`θ³ |∂³log(g(θ))/∂θ³| ≤ (2L₂θ³ + 8L₁θ²β)/g(0) + 5β³`.

**Formalization Note** `g, g′, g″` are assumed differentiable at every point of `[0, θ]`, the
reading under which `g⁽ᵖ⁾` (Definition 1) and the third derivative of `log g` at `θ` are the
classical ones; continuity of `g‴` is not assumed. The third derivative is
`iteratedDeriv 3 (fun t => Real.log (g t)) θ`. `L₁, L₂ ∈ (0, ∞)` is the frame of Definition 1. -/
theorem lemma_4 (g : ℝ → ℝ) (L₁ L₂ θ β : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hθ : 0 ≤ θ)
    (hdiff : ∀ k ≤ 2, ∀ t ∈ Set.Icc 0 θ, DifferentiableAt ℝ (iteratedDeriv k g) t)
    (hlip1 : HasLipDerivOn 1 L₁ g (Set.Icc 0 θ)) (hlip2 : HasLipDerivOn 2 L₂ g (Set.Icc 0 θ))
    (hg0 : 0 < g 0) (hβ : 0 < β) (hβ' : β ≤ 1 / 4)
    (hcond : |θ * deriv g 0| / g 0 + L₁ * θ ^ 2 / g 0 ≤ β) :
    (3 / 4 ≤ g θ / g 0 ∧ g θ / g 0 ≤ 4 / 3) ∧
      θ ^ 3 * |iteratedDeriv 3 (fun t => Real.log (g t)) θ| ≤
        (2 * L₂ * θ ^ 3 + 8 * L₁ * θ ^ 2 * β) / g 0 + 5 * β ^ 3 := by sorry

end TrustIPM
