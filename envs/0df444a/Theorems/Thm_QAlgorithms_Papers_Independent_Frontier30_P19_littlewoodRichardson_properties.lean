-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P19_littlewoodRichardson_properties
-- name    : QAlgorithms.Papers.Independent.Frontier30.P19.littlewoodRichardson_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:12:46.331841+00:00
-- url     : https://prove2.me/theorems/040e1bd7-a2ae-4c42-ba7c-4e776f53d55c
-- title:
--   Four properties of homogeneous Littlewood–Richardson coefficients
-- statement:
--   Let $d,m,n\ge1$ and let $\lambda,\mu,\nu$ be partitions of sizes $m,n,t$, respectively, with at most $d$ rows. Write $c_{\lambda,\mu}^{\nu}$ for the homogeneous Littlewood–Richardson coefficient, defined by the usual semistandard skew tableaux with lattice reading word, and write $\ell(\mu)$ for the number of nonzero rows of $\mu$. First,
--
--   $$c_{\lambda,\mu}^{\nu}=c_{\mu,\lambda}^{\nu}.$$
--
--   If $c_{\lambda,\mu}^{\nu}\ge1$, then all of the following hold:
--
--   1. $t=m+n$.
--   2. $\nu_i\ge\lambda_i$ for every $1\le i\le d$.
--   3. For any positive integers $i,k$ with $i+k-1\le d$, if $\nu_{i+k-1}>\lambda_i$, then $\ell(\mu)\ge k$.
--
--   In particular, the last implication bounds the height of a column of the skew diagram $\nu/\lambda$ by the number of available tableau letters. These properties control the sectors that can appear in tensor products.
--
--   **Formalization Note** The canonical polynomial, or degree-preserving $U(d)$, coefficient is used, as required by the source's own LR-tableau proof. The printed unused $j$ is interpreted as $i$. Lean numbers rows starting at zero.
-- source:
--   A memory and gate efficient algorithm for unitary mixed Schur sampling, arXiv:2410.15793v2, PDF p. 32, Lemma 11

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Lemma 11, all four clauses (arXiv:2410.15793v2, PDF p.32).
The positive d,m,n range is inherited from Definition 3 (N versus N_0).
Symmetry is unconditional; degree, containment and the column-height bound
are conclusions conditional on a nonzero coefficient.
Printed: SU(d) multiplicities with no homogeneous representative, unused j,
and i+k in the proof versus i+k-1 in the statement.
Changed: use the homogeneous polynomial/U(d) LR-tableau coefficient, read j
as i, and retain the statement's i+k-1 with positive k and valid row indices.
Why: determinant shifts identify different degrees over SU(d); the source's
LR-tableau proof selects degree m+n and a column of exactly k rows.
Lean's i is zero-based, so the final row is i+k-1 here. -/
theorem littlewoodRichardson_properties
    (d m n t : ℕ) (hd : 0 < d) (hm : 0 < m) (hn : 0 < n)
    (lambda : QAlgorithms.Schur.Partition d m)
    (mu : QAlgorithms.Schur.Partition d n)
    (nu : QAlgorithms.Schur.Partition d t) :
    lrCoefficient d lambda.val mu.val nu.val =
      lrCoefficient d mu.val lambda.val nu.val ∧
    (1 ≤ lrCoefficient d lambda.val mu.val nu.val →
      t = m + n ∧
      (∀ i : Fin d, lambda.val.rowLen i.val ≤ nu.val.rowLen i.val) ∧
      (∀ i k : ℕ, 0 < k → i + k ≤ d →
        lambda.val.rowLen i < nu.val.rowLen (i + k - 1) →
        k ≤ mu.val.colLen 0)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P19

end
