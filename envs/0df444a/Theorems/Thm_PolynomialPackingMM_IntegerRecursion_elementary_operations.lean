-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_elementary_operations
-- name    : PolynomialPackingMM.IntegerRecursion.elementary_operations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:09.092734+00:00
-- url     : https://prove2.me/theorems/59bac611-fbf6-4c01-abee-ad1e66dfb25a
-- title:
--   Observation 2.5 — elementary packing operations
-- statement:
--   A PP can zero-pad source matrix dimensions, delete targets or add unused sources, preserving its exact/modulo mode. Repeating it $k\ge1$ times gives
--
--   $$\#T_{\rm new}=k\#T,\quad\#S_{\rm new}=k\#S,\quad\operatorname{comp}(T_{\rm new},S_{\rm new})=\operatorname{comp}(T,S)$$
--
--   when the original source effort is positive. Deleting targets with the source list fixed also preserves SL-PPs. These structural operations provide the count adjustments used in the amplification and rounds.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - generalization: at least one monomial variable → the empty variable list is also allowed; reason: it is the tensor unit and the same formulas specialize to all source products
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
--   - encoding: the left encoder copies the one arbitrary common left input → the common left space is checked and the copying map is built into SLPackingData; reason: there is no left encoder that could mix or rescale the common input
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 10 (PDF 11), Observation 2.5; proof Appendix A.2, p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem elementary_operations :
  (∀ (mode : Mode) (T S S' : Tasks), HasPacking mode T S →
    SourcePadding S S' → HasPacking mode T S') ∧
  (∀ (mode : Mode) (T T' S : Tasks), HasPacking mode T S → T'.Sublist T →
    HasPacking mode T' S) ∧
  (∀ (mode : Mode) (T S U : Tasks), HasPacking mode T S → HasPacking mode T (S ++ U)) ∧
  (∀ (mode : Mode) (T S : Tasks) (k : ℕ+), HasPacking mode T S →
    HasPacking mode (repeatTasks k T) (repeatTasks k S) ∧
    (repeatTasks k T).length = (k : ℕ) * T.length ∧
    (repeatTasks k S).length = (k : ℕ) * S.length ∧
    (0 < totalEffort S → compression (repeatTasks k T) (repeatTasks k S) = compression T S)) ∧
  (∀ (mode : Mode) (T T' S : Tasks), HasSLPacking mode T S → T'.Sublist T →
    HasSLPacking mode T' S) := by sorry

end PolynomialPackingMM.IntegerRecursion
