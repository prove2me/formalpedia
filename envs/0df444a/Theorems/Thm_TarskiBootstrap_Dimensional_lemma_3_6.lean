-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_lemma_3_6
-- name    : TarskiBootstrap.Dimensional.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:18:19.022771+00:00
-- url     : https://prove2.me/theorems/4b87ef1e-dd0b-4669-bc38-ad020049b773
-- title:
--   Lemma 3.6 — Norm bound from summable projection overlaps
-- statement:
--   Let $A_1,\ldots,A_m$ be real symmetric idempotent $n\times n$ matrices. Let $a:\mathbb N\to\mathbb R$ satisfy $a_d>0$ for every $d$, with $\sum_{d=0}^\infty a_d$ convergent, and suppose
--
--   $$\forall i,j\in\{1,\ldots,m\},\quad\|A_iA_j\|_{2\to2}\le a_{|i-j|}.$$
--
--   Then
--
--   $$\left\|\sum_{i=1}^m A_i\right\|_{2\to2}\le a_0+2\sum_{d=1}^\infty a_d.$$
--
--   The sequence is arbitrary and strictly positive; orthogonality, commutativity, finite support and geometric decay are not assumed. The result controls sums of projections with nonzero overlaps.
--
--   Differences from the source:
--   - encoding: spectral matrix norm → operator norm of Matrix.toEuclideanCLM over real Euclidean space; reason: this is exactly the unnormalized real l2-to-l2 norm and removes matrix norm instance ambiguity
--   - encoding: one-based matrix indices and the absolute difference |i-j|; an infinite tail from d=1 → Fin m indices, Nat.dist, Summable a and the tail tsum of a(i+1); reason: shifting both indices leaves their absolute difference unchanged and a0 is counted exactly once
--   - generalization: the displayed list of m real n-by-n matrices → natural dimensions n and m also include empty matrices and empty lists; reason: the positive-dimensional source is included; when n=0 or m=0 the left side is zero and the positive summable envelope makes the right side nonnegative
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 3.6, equation (3.11), PDF/printed p. 14, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Witness

open scoped Matrix

namespace TarskiBootstrap.Dimensional

open scoped Classical

/-- Lemma 3.6, PDF/printed p. 14, with arbitrary positive summable overlap envelope. -/
theorem lemma_3_6 (n m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hsymm : ∀ i, (A i).IsSymm) (hidem : ∀ i, A i * A i = A i)
    (a : ℕ → ℝ) (hpositive : ∀ i, 0 < a i) (hsummable : Summable a)
    (hoverlap : ∀ i j, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A i * A j)‖ ≤ a (Nat.dist i.val j.val)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, A i)‖ ≤ a 0 + 2 * ∑' i : ℕ, a (i + 1) := by sorry

end TarskiBootstrap.Dimensional
