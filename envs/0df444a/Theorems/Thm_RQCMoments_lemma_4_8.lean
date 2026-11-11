-- Prove2me | Theorems.Thm_RQCMoments_lemma_4_8
-- name    : RQCMoments.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:08:27.936958+00:00
-- url     : https://prove2.me/theorems/f508ca6d-00bb-4ed9-ad92-bd777384c909
-- title:
--   Lemma 4.8 — bracketing $S_{i-1}\le F_\mu(x_i)\le S_i$ at the nodes of an exact quadrature
-- statement:
--   Let $\mu$ be a probability distribution on $\mathbb R$ with distribution function $F_\mu(x)=\mu((-\infty,x])$. For an integer $\ell\ge 2$ let $x_1<\dots<x_\ell$ and $w_1,\dots,w_\ell$ be the nodes and (real) weights of an $\ell$-node quadrature rule that is exact for $\mu$ on all polynomials of degree at most $2\ell-2$. With $S_i=\sum_{j\le i}w_j$ and $S_0=0$,
--   $$
--   S_{i-1}\le F_\mu(x_i)\le S_i\qquad\text{for all } i\in[\ell].
--   $$
--
--   These are the Chebyshev–Markov–Stieltjes inequalities; the proof of Theorem 4.9 applies them to $\mathrm{Beta}(1,N-1)$.
--
--   Differences from the source:
--
--   - encoding: a quadrature rule exact for μ on polynomials of degree ≤ 2ℓ − 2 → for each such g: g is μ-integrable and ∫ g dμ = Σ w_i g(x_i); reason: exactness presupposes that the integrals exist; Lean's Bochner integral of a non-integrable function is 0, and without integrability the hypothesis would not express exactness
--   - encoding: i ∈ [ℓ], S_i = Σ_{j≤i} w_j, S_0 = 0, F_μ(x_i) → i : Fin ℓ, Σ_{j<i} w_j ≤ (μ(Iic (x i))).toReal ≤ Σ_{j≤i} w_j; reason: 0-based reindexing (S_{i−1} is the sum over j < i); F_μ(x) = μ((−∞, x])
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.8, (93), p.28 (PDF p.30)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- **Lemma 4.8** (bracketing at the quadrature nodes) (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.8, p.28, PDF p.30).
Let `μ` be a probability distribution on `ℝ` with distribution function `F_μ`, and for an integer
`ℓ ≥ 2` let `x₁ < ⋯ < x_ℓ` and `w₁, …, w_ℓ` be the nodes and weights of an `ℓ`-node quadrature rule
that is exact for `μ` on all polynomials of degree at most `2ℓ − 2`. Then with `Sᵢ = ∑_{j≤i} wⱼ`
and `S₀ = 0`, `S_{i−1} ≤ F_μ(xᵢ) ≤ Sᵢ` for all `i` (93).

**Formalization Note** `F_μ(x) = μ((−∞, x])`. Exactness includes `μ`-integrability of each
polynomial of degree at most `2ℓ − 2`, which the paper's "exact for μ" presupposes (without it,
Lean's junk value `0` for non-integrable integrands would make the hypothesis meaningless). The
weights are arbitrary reals. With 0-based indices, `S_{i−1} = ∑_{j<i} wⱼ`. -/
theorem lemma_4_8 (μ : Measure ℝ) [IsProbabilityMeasure μ] (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (x : Fin ℓ → ℝ) (hx : StrictMono x) (w : Fin ℓ → ℝ)
    (hexact : ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * ℓ - 2 →
      Integrable (fun t => g.eval t) μ ∧ ∫ t, g.eval t ∂μ = ∑ i, w i * g.eval (x i)) :
    ∀ i : Fin ℓ, (∑ j ∈ Finset.Iio i, w j) ≤ (μ (Set.Iic (x i))).toReal ∧
      (μ (Set.Iic (x i))).toReal ≤ ∑ j ∈ Finset.Iic i, w j := by sorry

end RQCMoments
