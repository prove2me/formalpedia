-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_linearity_inputs
-- name    : PolynomialPackingMM.IntegerRecursion.linearity_inputs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:51.686877+00:00
-- url     : https://prove2.me/theorems/d3e7ee98-6f12-409c-9655-be375bda9ec4
-- title:
--   Lemma A.1 — linearity in the inputs
-- statement:
--   Let a PP have independent input lists $A,B$, or an SL-PP have one common left input $A$ and a right-input list $B$. For either exact or approximate mode, its decoded output $O$ and error $E=O-T$ satisfy
--
--   $$O(A+A',B)=O(A,B)+O(A',B),\qquad O(cA,B)=cO(A,B),$$
--
--   and the same identities in the right input and for $E$. These facts provide the input-linearity needed when composing and rescaling degenerations. **Formalization Note** All four additivity/homogeneity clauses are asserted for both the output and error, with Laurent scalars.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - generalization: at least one monomial variable → the empty variable list is also allowed; reason: it is the tensor unit and the same formulas specialize to all source products
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
--   - encoding: the left encoder copies the one arbitrary common left input → the common left space is checked and the copying map is built into SLPackingData; reason: there is no left encoder that could mix or rescale the common input
--   - generalization: linearity in the scalar input lists → linearity after extending the scalar inputs to Laurent coefficients; reason: the same finite bilinear formulas are linear over the Laurent coefficient ring and specialize to the source inputs
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 22 (PDF 23), Lemma A.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem linearity_inputs :
  (∀ (mode : Mode) (T S : Tasks) (D : PackingData T S), D.Valid mode →
    SeparatelyLinear D.evaluate ∧ SeparatelyLinear D.error) ∧
  (∀ (mode : Mode) (T S : Tasks) (D : SLPackingData T S), D.Valid mode →
    SeparatelyLinear D.output ∧ SeparatelyLinear D.error) := by sorry

end PolynomialPackingMM.IntegerRecursion
