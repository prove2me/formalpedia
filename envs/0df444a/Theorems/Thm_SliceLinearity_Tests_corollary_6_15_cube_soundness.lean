-- Prove2me | Theorems.Thm_SliceLinearity_Tests_corollary_6_15_cube_soundness
-- name    : SliceLinearity.Tests.corollary_6_15_cube_soundness
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:40:25.86794+00:00
-- url     : https://prove2.me/theorems/f7a04cd5-5213-418d-8276-14333ed7da14
-- title:
--   Corollary 6.15, proof step — on the p-biased cube the symmetric active-set test has soundness s(δ) = δ with no error
-- statement:
--   Let $0<p\le1/2$ and $m=\lceil1/p\rceil$. The $(m+1)$-query biased tester $\lambda_{p,m+1}^{\otimes n}$ has soundness guarantee $s(\delta)=\delta$ with no error term. That is, for every $n$ and every $f:\mathbb F_2^n\to\{\pm1\}$, if $f$ passes with probability at least $(1+\delta)/2$, then
--   $$\max_{\varphi\text{ affine}}\mathrm{agr}_{\mu_p}(f,\varphi)\ge\frac{1+\delta}2.$$
--   This is "By Lemma 6.13 with $m=\lceil1/p\rceil$, the test … as in the proof of Theorem 5.1, has soundness $s(\delta)=\delta$." The argument of Theorem 5.1 is: $\delta\le2\Pr[\text{accept}]-1=\mathbb E[f(x)\prod_jf(y_j)]\le\max_\chi|\langle f,\chi\rangle_{\mu_p}|$, and $\mathrm{agr}_{\mu_p}(f,\sigma\chi)=(1+\sigma\langle f,\chi\rangle_{\mu_p})/2$.
--
--   Differences from the source:
--   - encoding: f : F₂ⁿ → {±1}, signed characters σχ → f : F₂ⁿ → ZMod 2, affine maps x ↦ ⟨a,x⟩ + c, acceptance ∑ᵢ f(zᵢ) = 0 and agreement under μ_p; reason: σχ_ξ = (−1)^{⟨ξ,x⟩+c}; the product of ±1 answers is 1 iff the F₂ sum is 0; same instances
--   - encoding: δ in the soundness guarantee → 0 < δ ≤ 1; reason: the paper's convention for acceptance thresholds (Definition 2.4, p. 9)
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), proof of Corollary 6.15, p. 49 (PDF 51), by the argument of Theorem 5.1, p. 30 (PDF 32)

import Mathlib
import Definitions.Def_SliceLinearity_Tests_ActiveSet
import Definitions.Def_SliceLinearity_Tests_Transfer

set_option autoImplicit false

namespace SliceLinearity.Tests

/-- **Corollary 6.15, proof step** (cube soundness of the symmetric active-set test), p. 49 (PDF 51),
by the argument of Theorem 5.1, p. 30 (PDF 32). For `0 < p ≤ 1/2` and `m = ⌈1/p⌉`, the biased tester
`λ_{p,m+1}^{⊗n}` has soundness guarantee `s(δ) = δ` with no error: in every dimension, if `f` passes
with probability at least `(1 + δ)/2`, some affine map agrees with `f` under `μ_p` with probability
at least `(1 + δ)/2`. -/
theorem corollary_6_15_cube_soundness (p : ℝ) (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    SoundnessGuarantee p (lambdaPK p ⌈1 / p⌉₊) id := by sorry

end SliceLinearity.Tests
