-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_canonical_filters_real_symmetric
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.canonical_filters_real_symmetric
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:30:56.775974+00:00
-- url     : https://prove2.me/theorems/44d9f18c-c8ed-4b49-b87d-9e412fda04fc
-- title:
--   Canonical filters are real symmetric and Hermitian
-- statement:
--   Let $N\ge1$, $d\ge2$, and use exactly the canonical positive central filters $O$ and $\widetilde O$ from (A5) and (A9), respectively. The deterministic filter is formed from any real nonnegative unit principal eigenvector of the concrete dimension-truncated teleportation matrix. In the common computational orthonormal basis,
--
--   $$O=O^\dagger=\overline O=O^T,\qquad \widetilde O=\widetilde O^\dagger=\overline{\widetilde O}=\widetilde O^T.$$
--
--   These equalities justify moving these particular resource filters between Bell-pair factors. They do not follow merely from trace normalization of an arbitrary Alice operation.
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 21, Observation 11: the canonical optimization filters are real symmetric Hermitian

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Observation 11, PDF p.21 Eq.(B1): both canonical central filters are
Hermitian, entrywise real, and symmetric. This is not a claim about every resource filter. -/
theorem canonical_filters_real_symmetric (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (v : Schur.Partition d N → ℝ) (hv : IsPrincipal v) :
    (probabilisticFilter d N = (probabilisticFilter d N)ᴴ ∧
      probabilisticFilter d N = (probabilisticFilter d N).map (star : ℂ → ℂ) ∧
      probabilisticFilter d N = (probabilisticFilter d N)ᵀ) ∧
    (deterministicFilter v = (deterministicFilter v)ᴴ ∧
      deterministicFilter v = (deterministicFilter v).map (star : ℂ → ℂ) ∧
      deterministicFilter v = (deterministicFilter v)ᵀ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
