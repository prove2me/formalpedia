-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_l1_monotonicity
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.l1_monotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:24:01.379485+00:00
-- url     : https://prove2.me/theorems/fc1f399c-ca03-44c7-8902-9030ac24f7f3
-- title:
--   Selective and nonselective l1 monotonicity
-- statement:
--   Let $C_1(\rho)=\sum_{i\ne j}|\rho_{ij}|$. For every complete incoherent Kraus family on a positive-dimensional input, allowing different positive output dimensions, and every input density matrix,
--   $$\sum_{a:p_a>0}p_aC_1(p_a^{-1}K_a\rho K_a^\dagger)\le C_1(\rho),\qquad p_a=\operatorname{Tr}(K_a\rho K_a^\dagger).$$
--   When the output dimension is common, $C_1(\sum_aK_a\rho K_a^\dagger)\le C_1(\rho)$ as well. Incoherence is required separately of each branch; no individual-outcome decrease is asserted.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Appendix F (F.1)–(F.7), PDF p. 10. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P04

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq



























































/-- PDF pp.3,9–10, (F.1)–(F.7): average selective and nonselective l1 monotonicity. -/
theorem l1_monotonicity :
    CoherenceSelective (fun _ rho => Coherence.l1Coherence rho) ∧
    CoherenceMonotone (fun _ rho => Coherence.l1Coherence rho) := by sorry







end QAlgorithms.Papers.Independent.Independent1.P04
