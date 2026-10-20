-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_oneTooth_distance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.oneTooth_distance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:42:20.022898+00:00
-- url     : https://prove2.me/theorems/7261c5ca-113f-48a2-ae4b-a6d7a9e8ec71
-- title:
--   §V A Eq.(85): reduction to channel cb/diamond distance
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. For two quantum operations $\mathcal O_0,\mathcal O_1$ on a fixed one-tooth signature, let $d$ be half the maximal tester-normalized trace norm and let $d_{\rm cb}$ be half the supremum trace norm of their difference on a density operator with an arbitrary finite positive-dimensional ancilla. Then
--
--   $$
--   d_{\rm cb}(\mathcal O_0,\mathcal O_1)=d(C(\mathcal O_0),C(\mathcal O_1)).
--   $$
--
--   The cb distance is defined with the source factor $1/2$, independently of any library convention for the diamond norm.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 19, §V A Eq.(85): reduction to channel cb/diamond distance

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.19, Eq.(85): at one tooth the operational distance equals the source's
half-cb distance, also for trace-nonincreasing quantum operations. -/
theorem oneTooth_distance (s : Signature)
    (R S : Matrix (Basis s 1) (Basis s 1) ℂ)
    (hR : Probabilistic s 1 R) (hS : Probabilistic s 1 S) :
    cbDistance (parallelMap s 1 R) (parallelMap s 1 S) = combDistance s 1 R S := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
