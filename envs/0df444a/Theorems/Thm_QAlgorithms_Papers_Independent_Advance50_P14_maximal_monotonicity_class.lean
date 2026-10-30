-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_maximal_monotonicity_class
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.maximal_monotonicity_class
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:13:58.573811+00:00
-- url     : https://prove2.me/theorems/008b43da-3c4f-4a99-984b-e55a03ec9b48
-- title:
--   Section II unnumbered: maximal monotonicity class
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. An operation is CPTP; its separability constraint applies only to the specified input and output partitions. Fix an operation $\Lambda$ between any two such systems. Writing $R_G$ for global robustness, separability preservation is equivalent to monotonicity of each measure separately:
--
--   $$\Lambda\in{\rm SEPP}\iff[\forall\rho,\ E_R(\Lambda(\rho))\le E_R(\rho)],\qquad \Lambda\in{\rm SEPP}\iff[\forall\rho,\ R_G(\Lambda(\rho))\le R_G(\rho)].$$
--
--   The input quantifier ranges over all density matrices. Thus either measure identifies exactly the same maximal monotonicity class.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 4, Section II unnumbered: maximal monotonicity class

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.4: SEPP is exactly the monotonicity class for each of E_R and R_G
separately. Operations are CPTP; no ancillary extension is included. -/
theorem maximal_monotonicity_class {m l : ℕ} (A : MultipartiteRegister m) (B : MultipartiteRegister l)
    (L : Superop (RegisterBasis A.Local) (RegisterBasis B.Local)) (hL : IsChannel L) :
    (NonEntangling A B L ↔ ∀ rho : PartyOperator A, IsDensityMatrix rho →
      multipartiteRelativeEntanglement B (L rho) ≤ multipartiteRelativeEntanglement A rho) ∧
    (NonEntangling A B L ↔ ∀ rho : PartyOperator A, IsDensityMatrix rho →
      globalRobustness B (L rho) ≤ globalRobustness A rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
