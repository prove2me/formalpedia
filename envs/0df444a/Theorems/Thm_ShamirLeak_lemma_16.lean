-- Prove2me | Theorems.Thm_ShamirLeak_lemma_16
-- name    : ShamirLeak.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:29.575379+00:00
-- url     : https://prove2.me/theorems/56e7e9a1-2f98-45ad-9c16-4fac83495655
-- title:
--   Lemma 16 — bounds for a centered bit
-- statement:
--   Let $p$ be an odd prime and $\tau:\mathbb F_p\to\{0,1\}$. The function $f=2(\tau-\mathbb E[\tau])$, with $\mu=1-2\mathbb E[\tau]$, satisfies
--
--   $$\|f\|_2=\sqrt{1-\mu^2},\qquad\|f\|_{U^3}\le\kappa_0,\qquad\|f\|_\infty\le1+|\mu|\le2,$$
--
--   where $\kappa_0=(3/4)^{1/8}<1$. The $U^3$ bound is uniform over all one-bit maps, which is what lets Corollary 3 make the large supports exponentially small.
--
--   **Formalization Note** $\mathbb E[\tau]$ is the average over $\mathbb F_p$; the chain $\|f\|_\infty\le1+|\mu|\le2$ is two inequalities.
--
--   Differences from the source:
--   - encoding: τ : 𝔽_p → {0,1} → τ : ZMod p → Bool; reason: Lean convention ({0,1} as Bool, true = 1); same instances
-- source:
--   Nguyen, Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate, arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Lemma 16, p.31 (PDF 33); κ₀ from §6.2, p.31

import Mathlib
import Definitions.Def_ShamirLeak_chi
import Definitions.Def_ShamirLeak_gowersNorm
import Definitions.Def_ShamirLeak_bitFunctions
import Definitions.Def_ShamirLeak_constants

namespace ShamirLeak

/-- **Lemma 16 (Bounds for a centered bit)**, p.31 (PDF p.33). For every map `τ : 𝔽_p → {0, 1}` over an
odd prime field, the function `f = 2(τ − E[τ])`, with `µ = 1 − 2E[τ]`, satisfies
`‖f‖₂ = √(1 − µ²)`, `‖f‖_{U³} ≤ κ₀`, `‖f‖_∞ ≤ 1 + |µ| ≤ 2`, where `κ₀ = (3/4)^{1/8}`.
H. H. Nguyen, *Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate*,
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Lemma 16, p.31 (PDF p.33); `κ₀` from §6.2, p.31.

**Formalization Note.** `E[τ]` is the average of `τ` (as `0/1`) over the `p` elements of `𝔽_p`;
`f` is complex-valued with real values; all norms are under the uniform measure. The chain
`‖f‖_∞ ≤ 1 + |µ| ≤ 2` is stated as two inequalities. -/
theorem lemma_16 {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (τ : ZMod p → Bool) :
    let θ : ℝ := (∑ x : ZMod p, bitVal (τ x)) / p
    let f : ZMod p → ℂ := fun x => ((2 * (bitVal (τ x) - θ) : ℝ) : ℂ)
    let μ : ℝ := 1 - 2 * θ
    l2Norm f = Real.sqrt (1 - μ ^ 2) ∧ gowersNorm 3 f ≤ kappa0 ∧ supNorm f ≤ 1 + |μ| ∧
      1 + |μ| ≤ 2 := by sorry

end ShamirLeak
