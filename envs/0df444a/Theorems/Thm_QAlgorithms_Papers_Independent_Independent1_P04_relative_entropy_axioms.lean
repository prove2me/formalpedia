-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_relative_entropy_axioms
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.relative_entropy_axioms
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:24:17.453186+00:00
-- url     : https://prove2.me/theorems/806e4e5c-9287-4a83-8e67-335843661634
-- title:
--   Relative entropy is a proper coherence measure
-- statement:
--   In every positive finite dimension let $C_{\rm rel}(\rho)=S(\Delta\rho)-S(\rho)$, with natural logarithms. It is nonnegative, vanishes exactly on diagonal states, is convex, and is monotone under all complete incoherent operations. In particular, for selective operations with positive branch output dimensions,
--   $$\sum_{a:p_a>0}p_a C_{\rm rel}(\rho_a)\le C_{\rm rel}(\rho),\qquad p_a=\operatorname{Tr}(K_a\rho K_a^\dagger),\quad \rho_a=p_a^{-1}K_a\rho K_a^\dagger.$$
--   It also satisfies $C_{\rm rel}(\sum_a K_a\rho K_a^\dagger)\le C_{\rm rel}(\rho)$ when the output dimension is common. These clauses establish all the proper-coherence requirements; null branches are allowed.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, (C1’)–(C3), Appendix E (E.1)–(E.3), PDF p. 9. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

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
























































/-- PDF pp.2–3,8–9, (C1')–(C3), (E.1)–(E.3): all proper-coherence requirements. -/
theorem relative_entropy_axioms :
    CoherenceNonnegative entropyCoherence ∧ CoherenceFaithful entropyCoherence ∧
    CoherenceMonotone entropyCoherence ∧ CoherenceSelective entropyCoherence ∧
    CoherenceConvex entropyCoherence := by sorry










end QAlgorithms.Papers.Independent.Independent1.P04
