-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_relative_entropy_leakage
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.relative_entropy_leakage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:17:58.44399+00:00
-- url     : https://prove2.me/theorems/c44ed28e-3076-4832-8377-052861d079e7
-- title:
--   Lemma IV.5, equation (17): relative-entropy leakage bound
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. An operation is CPTP; its separability constraint applies only to the specified input and output partitions. If $\epsilon\ge0$ and $R_G(\Lambda(\sigma))\le\epsilon$ for every separable input $\sigma$, then for every density matrix $\rho$,
--
--   $$E_R(\Lambda(\rho))\le\log_2(1+\epsilon)+E_R(\rho).$$
--
--   The support-aware relative entropy is extended internally, while the minimum over separable comparison states is finite for these finite systems. The bound controls entropy leakage under the operational class.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 12, Lemma IV.5, equation (17): relative-entropy leakage bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF pp.12–13, Lemma IV.5, Eq.(17): additive relative-entropy leakage bound.
The ambient H in the printed SEPP(epsilon,H) does not impose ancillary closure. -/
theorem relative_entropy_leakage {m l : ℕ} (A : MultipartiteRegister m) (B : MultipartiteRegister l)
    (rho : PartyOperator A) (hrho : IsDensityMatrix rho) (epsilon : ℝ)
    (L : Superop (RegisterBasis A.Local) (RegisterBasis B.Local)) (hL : EpsilonNonEntangling A B epsilon L) :
    multipartiteRelativeEntanglement B (L rho) ≤ Real.logb 2 (1 + epsilon) +
      multipartiteRelativeEntanglement A rho := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
