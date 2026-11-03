-- Prove2me | Theorems.Thm_TrustIPM_taylor_eq_4
-- name    : TrustIPM.taylor_eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:48.805286+00:00
-- url     : https://prove2.me/theorems/3dd4c9de-3bcc-4c81-920e-1ab98b86b465
-- title:
--   Display (4) — Taylor's theorem with $L_p$-Lipschitz $p$th derivatives
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be $p+1$ times differentiable, let $\theta\in\mathbb R$, and suppose $g$ has $L_p$-Lipschitz $p$th derivatives on the interval between $0$ and $\theta$, $L_p\in(0,\infty)$. Then for every $q\in\{0,\dots,p\}$
--
--   $$
--   \Bigl|\sum_{i=0}^{p-q}\theta^i\frac{g^{(q+i)}(0)}{i!}-g^{(q)}(\theta)\Bigr|\le\frac{L_p|\theta|^{1+p-q}}{(1+p-q)!}.
--   $$
--
--   This is the Taylor estimate behind Lemmas 4–7: it bounds the error of a $(p-q)$th order expansion of $g^{(q)}$ by the Lipschitz constant of $g^{(p)}$.
--
--   **Formalization Note** "$p+1$ differentiable" means $g,\dots,g^{(p)}$ are differentiable on $\mathbb R$. The interval is `Set.uIcc 0 θ`, so negative $\theta$ is covered.
--
--   Differences from the source:
--   - reading: Lipschitz on the interval [0, θ], with the bound written in |θ| → Lipschitz on Set.uIcc 0 θ, for every real θ; reason: the bound in |θ| shows that both signs of θ are meant; for θ ≥ 0 the interval is [0, θ]
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, display (4), p.4

import Mathlib
import Definitions.Def_TrustIPM_HasLipDerivOn

namespace TrustIPM

/-- **Taylor's theorem, display (4)** (Hinder & Ye, *Worst-case iteration bounds for log barrier
methods on problems with nonconvex constraints*, arXiv:1807.00404v5, display (4), p.4). Let
`g : ℝ → ℝ` be `p + 1` times differentiable with `L_p`-Lipschitz `p`th derivatives on the interval
`[0, θ]`. Then for all `q ∈ {0, …, p}`,
`|Σ_{i=0}^{p−q} θⁱ g⁽ᵠ⁺ⁱ⁾(0)/i! − g⁽ᵠ⁾(θ)| ≤ L_p |θ|^{1+p−q}/(1 + p − q)!`.

**Formalization Note** "`p + 1` differentiable" is: `g, g′, …, g⁽ᵖ⁾` are differentiable on `ℝ`. The
interval "`[0, θ]`" is `Set.uIcc 0 θ`, so the statement covers every real `θ` (the bound is written
with `|θ|`). `L_p ∈ (0, ∞)` is the frame of Definition 1. -/
theorem taylor_eq_4 (g : ℝ → ℝ) (p : ℕ) (L θ : ℝ) (hL : 0 < L)
    (hdiff : ∀ k ≤ p, Differentiable ℝ (iteratedDeriv k g))
    (hlip : HasLipDerivOn p L g (Set.uIcc 0 θ)) :
    ∀ q ≤ p, |(∑ i ∈ Finset.range (p - q + 1),
        θ ^ i * iteratedDeriv (q + i) g 0 / (Nat.factorial i : ℝ)) - iteratedDeriv q g θ| ≤
      L * |θ| ^ (1 + p - q) / (Nat.factorial (1 + p - q) : ℝ) := by sorry

end TrustIPM
