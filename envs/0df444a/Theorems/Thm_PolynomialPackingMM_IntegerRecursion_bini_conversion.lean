-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_bini_conversion
-- name    : PolynomialPackingMM.IntegerRecursion.bini_conversion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:12.755445+00:00
-- url     : https://prove2.me/theorems/f63f5f27-1f87-4673-9079-ec304ecd6b8d
-- title:
--   Lemma 2.4 — approximate-to-exact conversion
-- statement:
--   Let $v\ge2$, $r\ge1$ and $\tau\in\mathbb R$. If multiplication of two $v\times v$ rational matrices has a rational bilinear algorithm modulo $\varepsilon$ of rank $r$ satisfying $r<v^\tau$, then there are $V\ge2$ and exact rational bilinear data of rank $R$ such that
--
--   $$R<V^\tau.$$
--
--   This removes the approximation parameter while retaining a strict finite-size exponent inequality. **Formalization Note** The input and output multiplication maps have arbitrary rational entries, and the coefficient identities specialize universally to characteristic-zero fields.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 10 (PDF 11), Lemma 2.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem bini_conversion :
  ∀ (v r : ℕ+) (τ : ℝ), 2 ≤ (v : ℕ) →
  (r : ℝ) < (v : ℝ) ^ τ → HasBilinearAlgorithm .approximate [matrixProduct v] r →
  ∃ (V : ℕ+) (R : ℕ), 2 ≤ (V : ℕ) ∧ (R : ℝ) < (V : ℝ) ^ τ ∧
    HasBilinearAlgorithm .exact [matrixProduct V] R := by sorry

end PolynomialPackingMM.IntegerRecursion
