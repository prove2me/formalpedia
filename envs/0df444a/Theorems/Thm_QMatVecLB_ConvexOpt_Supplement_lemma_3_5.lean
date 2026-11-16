-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_Supplement_lemma_3_5
-- name    : QMatVecLB.ConvexOpt.Supplement.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:21:50.799704+00:00
-- url     : https://prove2.me/theorems/7e09314d-241d-4412-8c11-df7ea75b0c01
-- title:
--   Lemma 3.5 — determinantal witnesses vanish on low-rank matrices
-- statement:
--   Let $b:\mathbb R^{n\times n}\to\mathbb R$ be a Schwartz function, let $\hat f(M)=\int e^{2\pi i\langle X,M\rangle}f(X)\,dX$ be the plus-sign Fourier transform of Eq. (18), and let $\beta=\det(-\frac1{2\pi i}\partial_X)b$ and $\beta_{I,J}=\det((-\frac1{2\pi i}\partial_X)_{I,J})b$ be the determinantal witnesses of Eqs. (23)–(24). Write $\mathcal R_r$ for the real $n\times n$ matrices of rank at most $r$.
--
--   1. For every $M\in\mathbb R^{n\times n}$,
--   $$\hat\beta(M)=\det(M)\,\hat b(M),$$
--   and $\hat\beta(M)=0$ for every $M\in\mathcal R_{n-1}$.
--   2. For all $I,J\subseteq[n]$ with $|I|=|J|=r+1$ and every $M$,
--   $$\hat\beta_{I,J}(M)=\det(M_{I,J})\,\hat b(M),$$
--   and $\hat\beta_{I,J}(M)=0$ for every $M\in\mathcal R_r$.
--
--   This makes $\beta$ a measure whose Fourier transform vanishes on $\mathcal R_{n-1}$, i.e. it satisfies condition (10) of the dual-witness definition; the trace and determinant-sign lower bounds start from it.
--
--   Differences from the source:
--   - encoding: Schwartz function on ℝ^{n×n} (sup_X |X^r ∂^s f(X)| < ∞ for all multi-indices r, s) → Mathlib SchwartzMap (RMat n) ℝ, with the entrywise sup norm on matrices; reason: all norms on a finite-dimensional space are equivalent, so the class is the page's; the same convention as the published lemma_3_4
--   - encoding: M ∈ R_{n−1} → M.rank < n; reason: the same set for n ≥ 1; for n = 0 the page's R_{−1} is empty, which rank < 0 matches, while natural-number subtraction would make rankVariety 0 (0−1) contain the 0×0 matrix
--   - encoding: subsets I, J ⊆ [n] with |I| = |J| = r+1 and the minor det(M_{I,J}) → Finsets with card r+1, enumerated increasingly (Finset.orderEmbOfFin) in both the operator minor and the matrix minor; reason: the standard minor convention; the same ordering is used on both sides of the identity
--   - encoding: Fourier transform (18) of the complex function β → the published fourierPlus (Bochner integral over the product Lebesgue measure matrixLebesgue); reason: identical definition
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 3.5, PDF p. 8 (printed p. 7).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Supplement_Witness

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt.Supplement
attribute [local instance] Classical.propDecidable

theorem lemma_3_5 (n : ℕ) (b : SchwartzMap (RMat n) ℝ) :
    (∀ M : RMat n, fourierPlus (detWitness (fun X => b X)) M =
        (M.det : ℂ) * fourierPlus (fun X => (b X : ℂ)) M) ∧
    (∀ M : RMat n, M.rank < n → fourierPlus (detWitness (fun X => b X)) M = 0) ∧
    (∀ (r : ℕ) (I J : Finset (Fin n)) (hI : I.card = r + 1) (hJ : J.card = r + 1) (M : RMat n),
        fourierPlus (minorWitness (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ) (fun X => b X)) M =
          ((M.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det : ℂ) *
            fourierPlus (fun X => (b X : ℂ)) M) ∧
    (∀ (r : ℕ) (I J : Finset (Fin n)) (hI : I.card = r + 1) (hJ : J.card = r + 1),
        ∀ M ∈ rankVariety n r,
          fourierPlus (minorWitness (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ) (fun X => b X)) M = 0) := by sorry

end QMatVecLB.ConvexOpt.Supplement
