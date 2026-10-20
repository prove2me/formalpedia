-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_sequentialDistance_dominatesParallel
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.sequentialDistance_dominatesParallel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:43:01.322013+00:00
-- url     : https://prove2.me/theorems/9d652bbd-f951-45bc-80b7-b8a1163e4a5d
-- title:
--   §V A Eq.(86): sequential distance dominates parallel distance
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $R,S$ be deterministic $N$-combs, $N\ge1$, and let $\mathcal R,\mathcal S$ be their multipartite channels viewed as parallel input/output maps. The distance based on sequential testers satisfies
--
--   $$
--   d(R,S)\ge d_{\rm cb}(\mathcal R,\mathcal S).
--   $$
--
--   The conclusion is non-strict. Both distances use half the trace norm, with the same fixed input/output wire roles.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 19, §V A Eq.(86): sequential distance dominates parallel distance

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.19, Eq.(86): parallel testers are included among sequential testers;
no assertion of strict inequality for every pair is made. -/
theorem sequentialDistance_dominatesParallel (s : Signature) (n : ℕ) (hn : 0 < n)
    (R S : Matrix (Basis s n) (Basis s n) ℂ)
    (hR : Deterministic n s R) (hS : Deterministic n s S) :
    cbDistance (parallelMap s n R) (parallelMap s n S) ≤ combDistance s n R S := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
