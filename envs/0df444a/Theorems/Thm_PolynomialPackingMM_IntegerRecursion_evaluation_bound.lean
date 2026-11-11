-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_evaluation_bound
-- name    : PolynomialPackingMM.IntegerRecursion.evaluation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:03.021374+00:00
-- url     : https://prove2.me/theorems/b1ab81ab-f46b-477c-ad17-3d5e6244cce9
-- title:
--   Lemma 2.3 — evaluation bound
-- statement:
--   For any selected matrix-polynomial product $P$, including products with an empty support, there is exact rational bilinear data of rank $r$ with
--
--   $$r\le\operatorname{eff}(P).$$
--
--   Correctness is universal coefficient matching, and counts only the $r$ scalar products of linear forms. This supplies the source-evaluation rank bound. **Formalization Note** The result includes every positive rectangular matrix dimension and arbitrary finite integer-exponent supports, not just univariate scalar products.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - generalization: at least one monomial variable → the empty variable list is also allowed; reason: it is the tensor unit and the same formulas specialize to all source products
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 10 (PDF 11), Lemma 2.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem evaluation_bound :
  ∀ P : SelectedProduct,
  ∃ r : ℕ, r ≤ P.effort ∧ HasBilinearAlgorithm .exact [P] r := by sorry

end PolynomialPackingMM.IntegerRecursion
