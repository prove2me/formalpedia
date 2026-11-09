-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_poisson_mixture_tv
-- name    : WangRenyiEntropy.Noninteger.poisson_mixture_tv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:31.048463+00:00
-- url     : https://prove2.me/theorems/88c70a4d-3b89-4a51-85ca-41238dea7910
-- title:
--   Lemma 2.3 — total variation of moment-matched Poisson mixtures
-- statement:
--   Let $M\ge0$ be finite and let $\nu_0,\nu_1$ be arbitrary real probability laws on $[0,M]$ matching the integer moments $1,\ldots,L$, where $L\ge1$ is an integer. If $L>2eM$, then
--   $$d_\mathrm{TV}(\mathbb E\operatorname{Poi}(U),\mathbb E\operatorname{Poi}(V))\le\left(\frac{2eM}{L}\right)^L.$$
--   Here $U\sim\nu_0$, $V\sim\nu_1$ and total variation is one half of the countable mass l1 distance. No finite-support or density condition is imposed. This is the full mixing-law inequality used to compare observation laws of matched priors.
--
--   Differences from the source:
--   - encoding: random variables supported on [0,M] and their moments → arbitrary Borel probability laws with full mass on the closed interval and their actual integrals; reason: the claims depend only on distributions; compact support gives finite moments at every positive order
--   - encoding: total variation on the natural count alphabet → half an extended nonnegative sum of absolute differences of mixture masses; reason: probability masses are finite and the distance is at most one; the extended sum retains the entire alphabet
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 6 / PDF 8, Lemma 2.3

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_MomentModel

open scoped ENNReal

namespace WangRenyiEntropy.Noninteger

/-- Lemma 2.3, printed p.6 / PDF p.8. Arbitrary real mixing laws. -/
theorem poisson_mixture_tv (M : ℝ) (hM : 0 ≤ M) (L : ℕ) (hL : 1 ≤ L)
    (ν₀ ν₁ : BoundedLaw M) (hmatch : MomentMatching L ν₀ ν₁)
    (hlarge : 2 * Real.exp 1 * M < (L : ℝ)) :
    mixtureTV ν₀ ν₁ ≤ ENNReal.ofReal ((2 * Real.exp 1 * M / L) ^ L) := by sorry

end WangRenyiEntropy.Noninteger
