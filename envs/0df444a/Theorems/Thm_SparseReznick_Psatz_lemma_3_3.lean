-- Prove2me | Theorems.Thm_SparseReznick_Psatz_lemma_3_3
-- name    : SparseReznick.Psatz.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:11.654809+00:00
-- url     : https://prove2.me/theorems/82469b10-c922-4b95-abf3-9714c56b9e86
-- title:
--   Lemma 3.3 — even functions on the sphere admit homogeneous approximants
-- statement:
--   For $n>0$, let $h:\mathbb R^n\to\mathbb R$ be even and continuous on the Euclidean unit sphere $S^{n-1}$. There is a sequence of homogeneous polynomials $q_k$ of degree $2k$ whose restrictions converge uniformly to $h$ on the sphere:
--
--   $$\sup_{x\in S^{n-1}}|q_k(x)-h(x)|\longrightarrow0.$$
--
--   This approximation supplies polynomial corrections on intersections of variable blocks. **Formalization Note** Exact total degree $2k$ is required, as printed; nonzero approximants can still converge to the zero function.
-- source:
--   Mai, Magron & Lasserre, A sparse version of Reznick’s Positivstellensatz, arXiv:2002.05101v2, p. 9, Lemma 3.3

import Mathlib

namespace SparseReznick.Psatz

theorem lemma_3_3 {n : ℕ} (hn : 0 < n) (h : (Fin n → ℝ) → ℝ)
    (heven : ∀ x, h (-x) = h x)
    (hcont : ContinuousOn h {x : Fin n → ℝ | ∑ i, x i ^ 2 = 1}) :
    ∃ q : ℕ → MvPolynomial (Fin n) ℝ,
      (∀ k, (q k).IsHomogeneous (2 * k) ∧ (q k).totalDegree = 2 * k) ∧
      TendstoUniformlyOn (fun k x => MvPolynomial.eval x (q k)) h Filter.atTop
        {x : Fin n → ℝ | ∑ i, x i ^ 2 = 1} := by sorry

end SparseReznick.Psatz
