-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_hellinger_shift
-- name    : WeightedSpectralSketch.LowerBound.hellinger_shift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:01:55.331803+00:00
-- url     : https://prove2.me/theorems/7e1679a0-2e00-41c9-a9a8-fc356d5d83ec
-- title:
--   Lemma 4.3 — Hellinger bound for a real shift
-- statement:
--   Let $X$ be a real random variable with density $p$ on $\mathbb R$, such that $u:=\sqrt p$ is absolutely continuous and $\int_{\mathbb R}|u'(z)|^2\,dz<\infty$. Then for every $h\in\mathbb R$,
--
--   $$
--   H^2(X,X+h)\le\frac{h^2}{2}\int_{\mathbb R}|u'(z)|^2\,dz .
--   $$
--
--   Applied to $Z=\tfrac12+\mathrm{Beta}(3,3)$, whose square-root density has $\int|u'|^2=10$, it gives $H^2(wZ,wZ+c)\le5c^2/w^2$ for every base weight $w>0$ and $c\in\mathbb R$, the per-edge estimate behind Lemma 4.4.
--
--   **Formalization Note.** The law of $X$ is Lebesgue measure with density $p$ ($p\ge0$ measurable, total mass $1$), and $X+h$ has the pushforward law under $z\mapsto z+h$. Absolute continuity of $u$ on $\mathbb R$ is stated on every compact interval (Mathlib's `AbsolutelyContinuousOnInterval`). $u'$ is Lean's `deriv`, which equals the almost-everywhere derivative of an absolutely continuous function. Both integrals are lower Lebesgue integrals in $[0,\infty]$.
--
--   Differences from the source:
--
--   - encoding: u = √p absolutely continuous on ℝ, derivative u′ → u absolutely continuous on every interval [a, b], derivative deriv u; reason: an absolutely continuous function on ℝ is one absolutely continuous on bounded intervals; deriv u agrees with u′ almost everywhere
--   - encoding: real integrals of p and |u′|² → lower Lebesgue integrals in [0, ∞]; reason: both integrands are nonnegative; finiteness is the stated hypothesis
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 11, Lemma 4.3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Stat

open MeasureTheory
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 4.3, p. 11: if `X` has density `p` on `ℝ` with `u = √p` absolutely continuous and
`∫ |u'|² < ∞`, then `H²(X, X + h) ≤ (h²/2) ∫ |u'(z)|² dz` for every real `h`. -/
theorem hellinger_shift (p : ℝ → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_meas : Measurable p)
    (hp_one : ∫⁻ z, ENNReal.ofReal (p z) = 1)
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun z => Real.sqrt (p z)) a b)
    (hfin : ∫⁻ z, ENNReal.ofReal (deriv (fun z => Real.sqrt (p z)) z ^ 2) < ⊤) (h : ℝ) :
    hellinger2 (volume.withDensity fun z => ENNReal.ofReal (p z))
        ((volume.withDensity fun z => ENNReal.ofReal (p z)).map fun z => z + h) ≤
      ENNReal.ofReal (h ^ 2 / 2) *
        ∫⁻ z, ENNReal.ofReal (deriv (fun z => Real.sqrt (p z)) z ^ 2) := by sorry

end WeightedSpectralSketch.LowerBound
