-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_tensor_consistency_iff_no_catalysis
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.tensor_consistency_iff_no_catalysis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:23:13.086506+00:00
-- url     : https://prove2.me/theorems/f8469804-5916-4ffc-b494-391db0325ea5
-- title:
--   Lemma VI.2, equation (24): tensor consistency iff no catalysis
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. Consider two global properties of the asymptotically non-entangling conversion relation. Tensor consistency means that, for every compatible pair of finite multipartite transformations, $\rho\prec\sigma$ and $\eta\prec\tau$ imply $\rho\otimes\eta\prec\sigma\otimes\tau$. Absence of catalysis means that for every finite multipartite pair and every fixed catalyst $\pi$, $\rho\otimes\pi\prec\sigma\otimes\pi$ implies $\rho\prec\sigma$. Then
--
--   $$\text{Tensor consistency}\quad\Longleftrightarrow\quad\text{absence of catalysis in every finite multipartite system}.$$
--
--   The same catalyst is returned asymptotically. Both sides are universally quantified theory properties; neither is asserted to hold unconditionally.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 19, Lemma VI.2, equation (24): tensor consistency iff no catalysis

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.19, Lemma VI.2, Eq.(24): equivalence of two GLOBAL theory
properties. It asserts neither tensor consistency nor absence of catalysts
unconditionally. The forward implication is attributed to Ref.[6] in the source. -/
theorem tensor_consistency_iff_no_catalysis :
    TensorConsistency ↔ ∀ m : ℕ, NoCatalysisAt m := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
