-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_round_product
-- name    : PolynomialPackingMM.IntegerRecursion.round_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:59.870947+00:00
-- url     : https://prove2.me/theorems/fd9d796e-785e-4691-aa4c-1953e7c7d7fd
-- title:
--   Lemma 4.1 — the product for a round
-- statement:
--   For every positive integer $d$, use the constructed shapes $T^d_{a,b}=(\mathrm{Full}_{a,b}\otimes\mathrm{Mid}_{a,b})^{\otimes d}$ and $Q^d_{a,b}=T^d_{a,b}\otimes(T^d_{a,b})^{12}\otimes(T^d_{a,b})^{13}$. For every $a,b\ge1$,
--
--   $$Q^d_{a,b}\cong Q^d_{b,a},\qquad \operatorname{eff}(Q^d_{a,b})=(a+b-1)^{6d}.$$
--
--   For every positive rectangular dimension triple $p,q,r$, $Q^d_{1,1}[p,q,r]$ is ordinary matrix multiplication with those dimensions. These are the parameter symmetry and matrix base case of a round. **Formalization Note** The base-case clause requires all three actual supports to equal the constant monomial, which fixes the selected product to ordinary multiplication.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - encoding: Q at a=b=1 is ordinary matrix multiplication → all three constructed supports are required to be the singleton constant monomial; reason: the selected-product evaluator is then exactly matrix multiplication with the stated dimensions
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 16 (PDF 17), Lemma 4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem round_product :
  ∀ (d a b : ℕ+),
  (roundShape d a b).Isomorphic (roundShape d b a) ∧
    (roundShape d a b).effort = ((a : ℕ) + b - 1) ^ (6 * (d : ℕ)) ∧
    ∀ p q r : ℕ+, IsOrdinaryMatrixProduct (product (roundShape d 1 1) p q r) := by sorry

end PolynomialPackingMM.IntegerRecursion
