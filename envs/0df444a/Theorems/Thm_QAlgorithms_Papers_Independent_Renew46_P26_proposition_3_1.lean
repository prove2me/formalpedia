-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_proposition_3_1
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.proposition_3_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:51:29.120499+00:00
-- url     : https://prove2.me/theorems/cedc17d6-3d93-4065-9915-f074f5206c0d
-- title:
--   Proposition 3.1
-- statement:
--   Let $T=(\lambda_0\nearrow\cdots\nearrow\lambda_n)$ be an actual branching path ending at $\lambda$, let $v_T$ be any nonzero vector of its canonical line, and let $1\leq k<n$. For the adjacent transposition $s_k=(k,k+1)$,
--
--   $$s_kv_T\in\sum_{T':\ \lambda'_j=\lambda_j\ (j\ne k)}V_{T'}.$$
--
--   Both endpoints and all levels other than $k$ remain fixed. Because this is a homogeneous span statement, arbitrary nonzero scaling of the source's unit vectors gives the same assertion.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 14, Proposition 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Proposition 3.1 (PDF p.14). Only level k=i+1 can change; all other
vertices, including both endpoints, remain fixed. The sum consists of the
actual canonical path subspaces, not arbitrary assigned eigenspaces. -/
theorem proposition_3_1 {n : ℕ} (C : IrreducibleClass n) (T : BranchingPathsToClass C)
    (i : Adjacent n) (v : Fin (classRepresentative C).dimension → ℂ)
    (hv : v ≠ 0) (hline : v ∈ canonicalLine C T.val) :
    (classRepresentative C).action (adjacentElement i) v ∈
      ⨆ U : {U : BranchingPath n // ∀ j : Fin (n + 1),
        j.val ≠ i.val.val + 1 → U.vertex j = T.val.vertex j},
        canonicalLine C U.val := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
