-- Prove2me | Theorems.Thm_RQCMoments_lemma_4_1
-- name    : RQCMoments.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:17.492456+00:00
-- url     : https://prove2.me/theorems/7a665ca2-9cb6-40af-b2c6-97a73b0dce35
-- title:
--   Lemma 4.1 — Gauss weights equal the Christoffel function at the nodes
-- statement:
--   Let $\nu$ be a probability distribution on $\mathbb R$ with infinite support, and $\ell\ge 1$. Let $x_1<\dots<x_\ell$ and $w_1,\dots,w_\ell$ be the nodes and weights of the $\ell$-node Gauss quadrature rule of $\nu$ (exact for all polynomials of degree at most $2\ell-1$). Then
--   $$
--   \lambda_{\nu,\ell}(x_i)=w_i\qquad\text{for all } i\in[\ell].
--   $$
--
--   The variational form of $w_i$ lets measure comparison bound quadrature weights (Theorem 4.4).
--
--   Differences from the source:
--
--   - generalization: the rule with nodes the roots of q_ℓ and weights ∫ ℓ_i dν, constructed as in §4.1 → every ℓ-node rule with strictly increasing nodes exact up to degree 2ℓ − 1 (IsGaussRule); reason: such a rule is unique and the paper's rule is one (gauss_exact), so the source's statement is the special case
--   - generalization: the orthonormal polynomial of degree ℓ of Section 2.4 (so moments finite up to order 2ℓ) → no moment hypothesis beyond the ν-integrability of polynomials of degree ≤ 2ℓ − 1 that IsGaussRule carries; reason: the proof uses only exactness of the rule; every ν the source allows has its Gauss rule satisfying IsGaussRule
--   - encoding: infinite support → no finite set s has ν(sᶜ) = 0; reason: equivalent for Borel measures on ℝ
--   - encoding: λ_{ν,ℓ} as a minimum (52) → christoffel: infimum over admissible polynomials with ν-integrable square; reason: the minimum is attained (Lemma 4.2); integrability only excludes undefined integrals
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_RQCMoments_IsGaussRule
import Definitions.Def_RQCMoments_christoffel

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- **Lemma 4.1** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.1, p.22, PDF p.24).
For a distribution `ν` on `ℝ` with infinite support, let `x₁ < ⋯ < x_ℓ` and `w₁, …, w_ℓ` be the
nodes and weights of its `ℓ`-node Gauss quadrature rule. Then `λ_{ν,ℓ}(xᵢ) = wᵢ` for all `i`.

**Formalization Note** "Infinite support" is: no finite set carries all of the mass. The statement
is made for every `ℓ`-node rule with strictly increasing nodes that is exact up to degree
`2ℓ − 1` (`IsGaussRule`, which includes `ν`-integrability of those polynomials); such a rule is
unique and is the one built from the roots of `q_ℓ` (§4.1). No moment hypothesis beyond the
integrability carried by `IsGaussRule` is imposed: the lemma itself assumes only infinite support,
and the proof uses only exactness. -/
theorem lemma_4_1 (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : ∀ s : Finset ℝ, ν ((s : Set ℝ)ᶜ) ≠ 0) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (x w : Fin ℓ → ℝ) (hrule : IsGaussRule ν ℓ x w) :
    ∀ i, christoffel ν ℓ (x i) = w i := by sorry

end RQCMoments
