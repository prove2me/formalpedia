-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_composition
-- name    : PolynomialPackingMM.IntegerRecursion.composition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:09.859528+00:00
-- url     : https://prove2.me/theorems/5acc7931-13cf-4daa-bd15-0dc9855400dc
-- title:
--   Lemma 2.9 — composition
-- statement:
--   If a PP packs $T$ using $S$ and another packs $S$ using $R$, both in exact mode or both modulo $\varepsilon$, there is a PP
--
--   $$T\ \text{using}\ R.$$
--
--   Its target and source counts are those of $T$ and $R$. If all three total efforts are positive, then $\operatorname{comp}(T,R)=\operatorname{comp}(T,S)\operatorname{comp}(S,R)$. This permits replacing every source computation by the next packing. **Formalization Note** The statement asserts existence of a valid composed packing; it does not prescribe unrescaled composition of two Laurent maps.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - generalization: at least one monomial variable → the empty variable list is also allowed; reason: it is the tensor unit and the same formulas specialize to all source products
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 11 (PDF 12), Lemma 2.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem composition :
  (∀ (mode : Mode) (T S R : Tasks),
    HasPacking mode T S → HasPacking mode S R → HasPacking mode T R) ∧
  (∀ T S R : Tasks, 0 < totalEffort T → 0 < totalEffort S → 0 < totalEffort R →
    compression T R = compression T S * compression S R) := by sorry

end PolynomialPackingMM.IntegerRecursion
