-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_common_positive_suboperator
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.common_positive_suboperator
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:25:32.495312+00:00
-- url     : https://prove2.me/theorems/87132237-fe17-4af9-8da2-7dccdcdbff60
-- title:
--   Lemma 25: fidelity bound from a common positive suboperator
-- statement:
--   Let H be a complex Hilbert space, with a complete orthonormal basis used only to compute traces. Let rho and sigma be positive trace-class operators of trace one, and let tau be positive trace class with rho-tau positive. With p=Tr(tau) and root fidelity F(rho,sigma)=Tr sqrt(sqrt(rho) sigma sqrt(rho)), the assertion is p F(tau/p,sigma) <= F(rho,sigma). At p=0 the weighted term is zero. No finite-dimensional, finite-rank, invertibility or positive-p restriction is imposed.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 68, Lemma 25: fidelity bound from a common positive suboperator

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.68, Lemma 25: normalized states on a general Hilbert space, including
infinite-dimensional systems. The basis is only a trace coordinate choice.
The weighted term at tau=0 is zero; no invertibility assumption is added. -/
theorem common_positive_suboperator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {I : Type*} (basis : HilbertBasis I ℂ H)
    (rho sigma : QAlgorithms.Papers.Independent.Dependency50.P13.State basis)
    (tau : QAlgorithms.Papers.Independent.Dependency50.P13.PositiveTraceClass H)
    (hdom : QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive
      (rho.val.val - tau.val.val)) :
    let p := (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace basis tau.val.val).re
    p * hilbertRootFidelity basis ((p : ℂ)⁻¹ • tau.val.val) sigma.val.val ≤
      hilbertRootFidelity basis rho.val.val sigma.val.val := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
