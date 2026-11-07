-- Prove2me | Theorems.Thm_QuadPTFLearn_lemma_6_3
-- name    : QuadPTFLearn.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:23:56.737743+00:00
-- url     : https://prove2.me/theorems/6e2458f1-0c7a-4823-8b16-59db60bbddd5
-- title:
--   Lemma 6.3 (identity), p.63 — $v^\top G_\ell v=\sum_{i=1}^{\ell} i\,B_i(v)^2$; the estimator clause is `lemma_6_3_estimator`
-- statement:
--   Let $D$ be a distribution over $\mathbb R^d\times\{0,1\}$ with $D_x=N(0,I)$ and $\ell\ge1$. Let $F_\ell=\mathrm{proj}_{\le\ell}(y)$ be the projection of $y$ onto polynomials of degree at most $\ell$ under the Gaussian distribution and $G_\ell=\mathbb E_{x\sim N(0,I)}[\nabla F_\ell(x)\nabla F_\ell(x)^\top]$. Then for every unit vector $v$,
--   $$v^\top G_\ell v=\sum_{i=1}^{\ell} i\,B_i^2(v),\qquad B_i(v)=\sup_{p(w)\in P_{\le\ell-i},\ \|p\|\le1}\mathbb E_{(x,y)\sim D}[y\,h_i(v\cdot x)\,p(w)].$$
--
--   The identity turns the search for high-influence directions into a spectral problem for the single matrix $G_\ell$.
--
--   This item is the first sentence of Lemma 6.3; its second sentence (the estimator for $G_\ell$) is the companion item `QuadPTFLearn.lemma_6_3_estimator`.
--
--   Differences from the source:
--   - encoding: D over ℝᵈ × {0,1} with D_x = N(0, I) → a probability law on ℝᵈ × ℝ with first marginal N(0, I_d) and label in {0,1} a.s.; reason: the same laws
--   - encoding: F_ℓ = proj_{≤ℓ}(y) → Σ_{|α|≤ℓ} E_D[y H_α(x)] H_α; reason: the H_α are an orthonormal basis; the same polynomial
--   - encoding: the supremum B_i(v) over p(w) ∈ P_{≤ℓ−i}, ∥p∥ ≤ 1 → the real sSup over polynomials on v⊥ of degree ≤ ℓ − i with Gaussian L² norm ≤ 1; reason: the set is nonempty and bounded above by ∥F_ℓ∥₂, so it is the page's supremum
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 6.3, first sentence, p.63 (PDF p.65)

import Mathlib
import Definitions.Def_QuadPTFLearn_Influence

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 6.3 (identity), p.63 (PDF p.65).

Let `D` be a distribution over `ℝᵈ × {0, 1}` with `D_x = N(0, I)` and `ℓ ≥ 1`. Let
`F_ℓ = proj_{≤ℓ}(y)` and `G_ℓ = E_{x∼N(0,I)}[∇F_ℓ(x) ∇F_ℓ(x)ᵀ]`. Then for every unit `v`,
`vᵀ G_ℓ v = Σ_{i=1}^{ℓ} i B_i(v)²`, where
`B_i(v) = sup_{p(w) ∈ P_{≤ℓ−i}, ‖p‖ ≤ 1} E_{(x,y)∼D}[y h_i(v · x) p(w)]`.

**Formalization Note.** The estimator clause of the same lemma is the companion item
`QuadPTFLearn.lemma_6_3_estimator`. -/
theorem lemma_6_3 {d : ℕ} (D : Measure (Pt d × ℝ)) [IsProbabilityMeasure D]
    (hD : IsBoolGaussLaw D) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (v : Pt d) (hv : ‖v‖ = 1) :
    ∑ i, ∑ j, v i * Gell D ℓ i j * v j =
      ∑ i ∈ Finset.Icc 1 ℓ, (i : ℝ) * Bcoef D ℓ v i ^ 2 := by sorry

end QuadPTFLearn
