-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_remove_same_left
-- name    : PolynomialPackingMM.IntegerRecursion.remove_same_left
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:03.281247+00:00
-- url     : https://prove2.me/theorems/3f26d82f-b99b-42dc-ba46-245003415dfe
-- title:
--   Lemma 3.4 — from SL-PP to PP
-- statement:
--   For positive integers $u,w,p,q,r$ and arbitrary shapes $F_1,\ldots,F_w,S$, an SL-PP modulo $\varepsilon$ of $(F_i[p,q,r])_{i=1}^w$ using $u$ copies of $S[p,q,r]$ gives a PP modulo $\varepsilon$ of
--
--   $$(F_i[p,q,wr])_{i=1}^w\quad\text{using}\quad(2w-1)\,S[p,q,ur].$$
--
--   The new target left inputs are independent. This is the transition that permits separate target renamings. **Formalization Note** Shapes need not agree; their common left space is supplied by the SL-PP hypothesis, and $w=1$ remains included.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - generalization: at least one monomial variable → the empty variable list is also allowed; reason: it is the tensor unit and the same formulas specialize to all source products
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
--   - encoding: the left encoder copies the one arbitrary common left input → the common left space is checked and the copying map is built into SLPackingData; reason: there is no left encoder that could mix or rescale the common input
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 15 (PDF 16), Lemma 3.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem remove_same_left :
  ∀ (u w p q r : ℕ+) (F : Fin (w : ℕ) → Shape) (S : Shape),
  HasSLPacking .approximate (List.ofFn (fun i => product (F i) p q r))
    (copies u (product S p q r)) →
  HasPacking .approximate (List.ofFn (fun i => product (F i) p q (w * r)))
    (copies (2 * (w : ℕ) - 1) (product S p q (u * r))) := by sorry

end PolynomialPackingMM.IntegerRecursion
