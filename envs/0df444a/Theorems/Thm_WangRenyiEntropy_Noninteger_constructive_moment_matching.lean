-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_constructive_moment_matching
-- name    : WangRenyiEntropy.Noninteger.constructive_moment_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:13.918815+00:00
-- url     : https://prove2.me/theorems/47aa1b88-6159-4314-921f-cc6e5c0181df
-- title:
--   Lemma 3.1 — matching moments with separated fractional moments
-- statement:
--   Fix any positive noninteger real $\alpha$ and real $R>1$. There exists $c_{\alpha,R}>0$, independent of the integer $K\ge2$, such that for every such $K$ there are probability measures $\nu_0,\nu_1$ on $[0,K^2]$ matching all integer moments $1,\ldots,K$. With common mean $\mu$ and moments $\mu_b^{(q)}=\mathbb E_{X\sim\nu_b}X^q$, both laws satisfy
--   $$c_{\alpha,R}\le\mu,\mu_b^{(2)},\mu_b^{(\alpha)},\mu_b^{(2\alpha)}\le2,\qquad \mu_1^{(\alpha)}\ge R\mu_0^{(\alpha)}.$$
--   The uniform high-moment bounds and multiplicative separation, together with exact moment matching, are the complete conclusion. They provide the source's bounded-moment hard-prior interface; no indistinguishability conclusion is assumed.
--
--   Differences from the source:
--   - encoding: random variables supported on [0,M] and their moments → arbitrary Borel probability laws with full mass on the closed interval and their actual integrals; reason: the claims depend only on distributions; compact support gives finite moments at every positive order
--   - encoding: integer K ≥ 2 and noninteger positive α → natural K ≥ 2 and positive real α unequal to every natural integer; reason: these domains coincide under positivity; both means agree because order one is matched
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 7 / PDF 9, Lemma 3.1, Eqs. (7)–(8)

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_SamplingExperiment
import Definitions.Def_WangRenyiEntropy_Noninteger_MomentModel

open MeasureTheory

namespace WangRenyiEntropy.Noninteger

/-- Lemma 3.1, printed p.7 / PDF p.9, including all bounds in (7) and (8).
The common lower bound is independent of K. -/
theorem constructive_moment_matching (α R : ℝ) (hα : NonintegerOrder α) (hR : 1 < R) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, 2 ≤ K →
      ∃ ν₀ ν₁ : BoundedLaw ((K : ℝ) ^ 2),
        MomentMatching K ν₀ ν₁ ∧
        c ≤ moment ν₀ 1 ∧ moment ν₀ 1 ≤ 2 ∧
        (∀ ν ∈ ({ν₀, ν₁} : Set (BoundedLaw ((K : ℝ) ^ 2))),
          ∀ q ∈ ({(2 : ℝ), α, 2 * α} : Set ℝ),
            c ≤ moment ν q ∧ moment ν q ≤ 2) ∧
        moment ν₁ α ≥ R * moment ν₀ α := by sorry

end WangRenyiEntropy.Noninteger
