-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_tensoring_packings
-- name    : PolynomialPackingMM.IntegerRecursion.tensoring_packings
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:01.553097+00:00
-- url     : https://prove2.me/theorems/e1415074-2479-4285-b2f5-e9c50bd4eb2e
-- title:
--   Lemma 2.7 — tensoring packings
-- statement:
--   Suppose two PPs pack $T$ using $S$ and $T'$ using $S'$, in one fixed exact/modulo mode. There is a packing
--
--   $$(T_i\otimes T'_k)_{i,k}\ \text{using}\ (S_j\otimes S'_\ell)_{j,\ell},$$
--
--   with the products of the respective target and source counts. If their fully decoded outputs have degrees at most $d_\varepsilon,d'_\varepsilon$, the combined output has degree at most $d_\varepsilon+d'_\varepsilon$. The entire assertion also holds for SL-PPs. For all selected products, $\operatorname{eff}(P\otimes Q)=\operatorname{eff}(P)\operatorname{eff}(Q)$, and compression rates multiply when both source efforts are positive. This controls both savings and parameter degrees under amplification.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - generalization: at least one monomial variable → the empty variable list is also allowed; reason: it is the tensor unit and the same formulas specialize to all source products
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
--   - encoding: the left encoder copies the one arbitrary common left input → the common left space is checked and the copying map is built into SLPackingData; reason: there is no left encoder that could mix or rescale the common input
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 11 (PDF 12), Lemma 2.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem tensoring_packings :
  (∀ (mode : Mode) (T S T' S' : Tasks)
    (D : PackingData T S) (E : PackingData T' S'), D.Valid mode → E.Valid mode →
    ∃ C : PackingData (tensorTasks T T') (tensorTasks S S'), C.Valid mode ∧
      (tensorTasks T T').length = T.length * T'.length ∧
      (tensorTasks S S').length = S.length * S'.length ∧
      ∀ d d' : ℕ, D.DegreeAtMost d → E.DegreeAtMost d' → C.DegreeAtMost (d + d')) ∧
  (∀ (mode : Mode) (T S T' S' : Tasks)
    (D : SLPackingData T S) (E : SLPackingData T' S'), D.Valid mode → E.Valid mode →
    ∃ C : SLPackingData (tensorTasks T T') (tensorTasks S S'), C.Valid mode ∧
      (tensorTasks T T').length = T.length * T'.length ∧
      (tensorTasks S S').length = S.length * S'.length ∧
      ∀ d d' : ℕ, D.DegreeAtMost d → E.DegreeAtMost d' → C.DegreeAtMost (d + d')) ∧
  (∀ P Q : SelectedProduct, (P.tensor Q).effort = P.effort * Q.effort) ∧
  (∀ T S T' S' : Tasks, 0 < totalEffort S → 0 < totalEffort S' →
    compression (tensorTasks T T') (tensorTasks S S') = compression T S * compression T' S') := by sorry

end PolynomialPackingMM.IntegerRecursion
