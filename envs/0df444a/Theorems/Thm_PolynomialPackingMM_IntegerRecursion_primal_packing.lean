-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_primal_packing
-- name    : PolynomialPackingMM.IntegerRecursion.primal_packing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:03.952891+00:00
-- url     : https://prove2.me/theorems/e2541732-758b-4e61-a27f-11240cbae6bc
-- title:
--   Theorem 3.1 — primal packing
-- statement:
--   For all positive integers $a,b,c,t,p,q,r$ satisfying $ct\ge a+2b-1$, there is an SL-PP modulo $\varepsilon$ of
--
--   $$(c+1)\,\mathrm{Full}_{a,b}[p,q,r]\ +\ \mathrm{Mid}_{a,b}[p,q,r]\quad\text{using}\quad c\,\mathrm{Full}_{a,b+t}[p,q,r].$$
--
--   The $c+1$ full right inputs and the middle right input are independent, and all share one arbitrary left input copied unchanged. This is the primal packing used in the amplification chain. **Formalization Note** Mid uses the shifted negative exponents of equation (2), and the case $c=1$ is retained.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
--   - encoding: the left encoder copies the one arbitrary common left input → the common left space is checked and the copying map is built into SLPackingData; reason: there is no left encoder that could mix or rescale the common input
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 12 (PDF 13), Theorem 3.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem primal_packing :
  ∀ (a b c t p q r : ℕ+), (a : ℕ) + 2 * (b : ℕ) - 1 ≤ (c : ℕ) * t →
  HasSLPacking .approximate
    (copies ((c : ℕ) + 1) (product (full a b) p q r) ++ [product (mid a b) p q r])
    (copies c (product (full a ((b : ℕ) + t)) p q r)) := by sorry

end PolynomialPackingMM.IntegerRecursion
