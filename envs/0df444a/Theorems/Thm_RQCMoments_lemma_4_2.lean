-- Prove2me | Theorems.Thm_RQCMoments_lemma_4_2
-- name    : RQCMoments.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:21.907877+00:00
-- url     : https://prove2.me/theorems/c3a5099b-8020-491c-acb7-e7e19d1f08f8
-- title:
--   Lemma 4.2 — $\lambda_{\nu,\ell}(x)=\int p_x^2\,d\nu=1/\sum_{j<\ell}q_j(x)^2$
-- statement:
--   Let $\nu$ be a probability distribution on $\mathbb R$ with finite moments and infinite support, $\ell\ge 1$ an integer, and $q_j$ the orthonormal polynomials of $\nu$. For $x\in\mathbb R$ let
--   $$
--   p_x(t)=\frac{\sum_{j=0}^{\ell-1}q_j(x)\,q_j(t)}{\sum_{j=0}^{\ell-1}q_j(x)^2}.
--   $$
--   Then
--   $$
--   \lambda_{\nu,\ell}(x)=\int_{\mathbb R}p_x(t)^2\,d\nu(t)=\frac{1}{\sum_{j=0}^{\ell-1}q_j(x)^2}.
--   $$
--
--   The closed form underlies the Chebyshev computation in Lemma 4.3.
--
--   **Formalization Note** The statement holds for any orthonormal family (they differ by signs, which cancel).
--
--   Differences from the source:
--
--   - encoding: λ_{ν,ℓ} as a minimum (52) → christoffel: infimum over admissible polynomials with ν-integrable square; reason: the minimum is attained (this lemma); integrability only excludes undefined integrals
--   - encoding: ν with finite moments and infinite support (as in Section 2.4) → IsOPMeasure ν; reason: the §2.4 assumption, with infinite support as 'no finite set carries all mass'
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.2, (54)–(55), p.22 (PDF p.24)

import Mathlib
import Definitions.Def_RQCMoments_IsOPMeasure
import Definitions.Def_RQCMoments_IsOrthonormalFamily
import Definitions.Def_RQCMoments_christoffel

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- **Lemma 4.2** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.2, pp.22–23, PDF pp.24–25).
For `ν` with finite moments and infinite support and an integer `ℓ ≥ 1`, with `qⱼ` the
orthonormal polynomials of `ν` and
`pₓ(t) = ∑_{j<ℓ} qⱼ(x) qⱼ(t) / ∑_{j<ℓ} qⱼ(x)²` (54),
`λ_{ν,ℓ}(x) = ∫ pₓ(t)² dν(t) = 1 / ∑_{j<ℓ} qⱼ(x)²` (55), for every real `x`.

**Formalization Note** Holds for any orthonormal family (they differ only by signs, which cancel). -/
theorem lemma_4_2 (ν : Measure ℝ) (hν : IsOPMeasure ν) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (q : ℕ → Polynomial ℝ) (hq : IsOrthonormalFamily ν q) (x : ℝ) :
    let S : ℝ := ∑ j ∈ Finset.range ℓ, ((q j).eval x) ^ 2
    let px : Polynomial ℝ :=
      (∑ j ∈ Finset.range ℓ, Polynomial.C ((q j).eval x) * q j) * Polynomial.C (1 / S)
    christoffel ν ℓ x = ∫ t, (px.eval t) ^ 2 ∂ν ∧ christoffel ν ℓ x = 1 / S := by sorry

end RQCMoments
