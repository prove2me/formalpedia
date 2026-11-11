-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_role_exchanges
-- name    : PolynomialPackingMM.IntegerRecursion.role_exchanges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:05.461224+00:00
-- url     : https://prove2.me/theorems/c501342d-5c09-40b2-bb76-38123ef290a4
-- title:
--   Lemma 2.8 — role exchanges for packings
-- statement:
--   Let a PP pack a finite list $(T_i)$ using $(S_j)$, exactly or modulo $\varepsilon$. For every permutation $\sigma$ of the three roles, there is a PP
--
--   $$(T_i^\sigma)_i\ \text{using}\ (S_j^\sigma)_j.$$
--
--   Both list lengths and each selected product's effort are preserved. For $\sigma=(23)$ the same assertion holds for SL-PPs. Successive exchanges satisfy $(P^\sigma)^\tau=P^{\tau\sigma}$. These transformations supply the dual and the other dimension reductions. **Formalization Note** Role permutations act on $(I,J,-K)$ and permute shared matrix indices; no commutativity of matrix factors is used.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - generalization: at least one monomial variable → the empty variable list is also allowed; reason: it is the tensor unit and the same formulas specialize to all source products
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
--   - encoding: the left encoder copies the one arbitrary common left input → the common left space is checked and the copying map is built into SLPackingData; reason: there is no left encoder that could mix or rescale the common input
--   - encoding: successive role exchanges from §2.1 → the composition law is included with Lemma 2.8; reason: this records the source convention used by the milestone
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 11 (PDF 12), Lemma 2.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem role_exchanges :
  (∀ (mode : Mode) (T S : Tasks) (σ : Equiv.Perm (Fin 3)),
    HasPacking mode T S →
      HasPacking mode (exchangeTasks T σ) (exchangeTasks S σ) ∧
      (exchangeTasks T σ).length = T.length ∧ (exchangeTasks S σ).length = S.length) ∧
  (∀ (P : SelectedProduct) (σ : Equiv.Perm (Fin 3)), (P.exchange σ).effort = P.effort) ∧
  (∀ (mode : Mode) (T S : Tasks), HasSLPacking mode T S →
    HasSLPacking mode (exchangeTasks T swap23) (exchangeTasks S swap23)) ∧
  (∀ (P : SelectedProduct) (σ τ : Equiv.Perm (Fin 3)),
    (P.exchange σ).exchange τ = P.exchange (τ * σ)) := by sorry

end PolynomialPackingMM.IntegerRecursion
