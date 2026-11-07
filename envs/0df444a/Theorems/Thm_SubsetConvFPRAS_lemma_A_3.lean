-- Prove2me | Theorems.Thm_SubsetConvFPRAS_lemma_A_3
-- name    : SubsetConvFPRAS.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:06.337459+00:00
-- url     : https://prove2.me/theorems/20fbd7e0-7318-4c8b-b4fa-d127c67d7944
-- title:
--   Lemma A.3 — homogeneous parts of a multiaffine log-concave polynomial are zero or log-concave
-- statement:
--   Let $g=g_\mu$ be a multiaffine log-concave polynomial with nonnegative coefficients. For each degree $k$, the sum of the degree-$k$ terms of $g$,
--   $$g_k(x)=\sum_{|S|=k}\mu(S)\,x^S,$$
--   is either zero or log-concave.
--
--   This is the step of Theorem 1.6 that splits a non-homogeneous pair into the homogeneous layers handled by Theorem 5.1.
--
--   Differences from the source:
--   - encoding: a multiaffine polynomial g and its degree-k part → its coefficient weight μ and the weight keeping the sets of size k; reason: a multiaffine polynomial is determined by its coefficients
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Lemma A.3, p.35 (citing Robinson, Sun, Jeronimo 2019, Corollary 28)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_SetWeights

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Lemma A.3 ([RSJ19, Corollary 28]), p.35. For a multiaffine log-concave
polynomial with nonnegative coefficients and each degree `k`, the sum of the degree-`k` terms is zero or log-concave.

**Formalization Note.** A multiaffine polynomial is given by its coefficient weight `μ`; `homogPart μ k` keeps the
coefficients of the sets of size `k`. -/
theorem lemma_A_3 {U : Type} [Fintype U] [DecidableEq U] (μ : Finset U → ℝ)
    (hμ : ∀ S, 0 ≤ μ S) (hlc : IsLogConcave μ) (k : ℕ) :
    (∀ S, homogPart μ k S = 0) ∨ IsLogConcave (homogPart μ k) := by sorry

end SubsetConvFPRAS
