-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_shape_isomorphism
-- name    : PolynomialPackingMM.IntegerRecursion.shape_isomorphism
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:52.449043+00:00
-- url     : https://prove2.me/theorems/866a3514-b6ac-4163-b551-017dbc1c3790
-- title:
--   Lemma 2.10 — isomorphism
-- statement:
--   Shapes are isomorphic when one variable-coordinate permutation carries all three supports to the other shape. This relation is reflexive, symmetric and transitive, and
--
--   $$(P\otimes Q)\otimes R\cong P\otimes(Q\otimes R),\quad P\otimes Q\cong Q\otimes P,\quad (P\otimes Q)^\sigma\cong P^\sigma\otimes Q^\sigma.$$
--
--   Isomorphism respects role exchanges and tensoring of two isomorphic pairs. Replacing any PP target or source by an isomorphic selected product preserves both counts and exact/modulo validity. Applying a single common variable renaming to every task also preserves SL-PPs. This permits canonical shapes without silently identifying independent common left inputs.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - generalization: at least one monomial variable → the empty variable list is also allowed; reason: it is the tensor unit and the same formulas specialize to all source products
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
--   - encoding: the left encoder copies the one arbitrary common left input → the common left space is checked and the copying map is built into SLPackingData; reason: there is no left encoder that could mix or rescale the common input
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 12 (PDF 13), Lemma 2.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem shape_isomorphism :
  (∀ P : Shape, P.Isomorphic P) ∧
  (∀ P Q : Shape, P.Isomorphic Q → Q.Isomorphic P) ∧
  (∀ P Q R : Shape, P.Isomorphic Q → Q.Isomorphic R → P.Isomorphic R) ∧
  (∀ P Q R : Shape, ((P.tensor Q).tensor R).Isomorphic (P.tensor (Q.tensor R))) ∧
  (∀ P Q : Shape, (P.tensor Q).Isomorphic (Q.tensor P)) ∧
  (∀ (P Q : Shape) (σ : Equiv.Perm (Fin 3)),
    ((P.tensor Q).exchange σ).Isomorphic ((P.exchange σ).tensor (Q.exchange σ))) ∧
  (∀ (P Q : Shape) (σ : Equiv.Perm (Fin 3)), P.Isomorphic Q →
    (P.exchange σ).Isomorphic (Q.exchange σ)) ∧
  (∀ P Q P' Q' : Shape, P.Isomorphic Q → P'.Isomorphic Q' →
    (P.tensor P').Isomorphic (Q.tensor Q')) ∧
  (∀ (mode : Mode) (T S T' S' : Tasks), HasPacking mode T S →
    TasksIsomorphic T T' → TasksIsomorphic S S' →
    HasPacking mode T' S' ∧ T'.length = T.length ∧ S'.length = S.length) ∧
  (∀ (mode : Mode) (T S T' S' : Tasks), HasSLPacking mode T S →
    CommonRenaming T S T' S' →
    HasSLPacking mode T' S' ∧ T'.length = T.length ∧ S'.length = S.length) := by sorry

end PolynomialPackingMM.IntegerRecursion
