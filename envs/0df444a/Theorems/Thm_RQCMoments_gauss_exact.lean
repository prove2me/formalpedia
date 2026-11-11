-- Prove2me | Theorems.Thm_RQCMoments_gauss_exact
-- name    : RQCMoments.gauss_exact
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:12.497818+00:00
-- url     : https://prove2.me/theorems/bd313835-40f0-471d-b23d-22b13c2ae226
-- title:
--   §4.1, (50)–(51) — Gauss quadrature at the zeros of $q_\ell$ is exact to degree $2\ell-1$
-- statement:
--   Let $\nu$ be a probability measure on $\mathbb R$ with finite moments and infinite support, $q_0,q_1,\dots$ its orthonormal polynomials, and $\ell\ge 1$. Let $x_1<\dots<x_\ell$ be the zeros of $q_\ell$, let $\ell_i$ be the Lagrange basis polynomial of degree $\ell-1$ with $\ell_i(x_j)=\delta_{ij}$, and put $w_i=\int\ell_i\,d\nu$. Then
--   $$
--   \int g\,d\nu=\sum_{i=1}^{\ell}w_i\,g(x_i)\qquad\text{for every real polynomial } g \text{ of degree at most } 2\ell-1 .
--   $$
--
--   This is the exactness property (95) used in the proof of Theorem 4.9, with $\nu=\mathrm{Beta}(1,N-1)$ and $\ell=k+1$.
--
--   Differences from the source:
--
--   - generalization: μ_{a,D} = Beta(a, D) (the paper notes the method applies to other distributions and uses it with ν in Lemma 4.1) → every probability measure ν on ℝ with finite moments and infinite support; reason: Beta(a, D) with integers a, D ≥ 1 has finite moments and infinite support, so the source's case is an instance
--   - encoding: ∫ g dμ = Σ w_i g(x_i) for deg g ≤ 2ℓ − 1 → IsGaussRule ν ℓ x w, which also records ν-integrability of each such g; reason: integrability holds automatically under finite moments; same content
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), §4.1, (50)–(51), p.21 (PDF p.23)

import Mathlib
import Definitions.Def_RQCMoments_IsOPMeasure
import Definitions.Def_RQCMoments_IsOrthonormalFamily
import Definitions.Def_RQCMoments_IsGaussRule

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- **§4.1, (50)–(51): exactness of Gauss quadrature** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), §4.1, (50)–(51), p.21, PDF p.23).
Let `ν` be as in §2.4, `q` its orthonormal polynomials, `ℓ ≥ 1`, `x₁ < ⋯ < x_ℓ` the roots of
`q_ℓ`, `ℓᵢ` the Lagrange basis polynomial with `ℓᵢ(xⱼ) = δᵢⱼ`, and `wᵢ = ∫ ℓᵢ dν`. Then
`∫ g dν = ∑ᵢ wᵢ g(xᵢ)` for every polynomial `g` of degree at most `2ℓ − 1`.

**Formalization Note** The conclusion is `IsGaussRule ν ℓ x w`, which also records that each such `g`
is `ν`-integrable (automatic under finite moments). The paper states this for `Beta(a, D)` and
applies it to general `ν` in Lemma 4.1. -/
theorem gauss_exact (ν : Measure ℝ) (hν : IsOPMeasure ν) (q : ℕ → Polynomial ℝ)
    (hq : IsOrthonormalFamily ν q) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (x : Fin ℓ → ℝ) (hx : StrictMono x)
    (hroots : (q ℓ).roots = Multiset.map x Finset.univ.val) :
    IsGaussRule ν ℓ x (fun i => ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂ν) := by sorry

end RQCMoments
