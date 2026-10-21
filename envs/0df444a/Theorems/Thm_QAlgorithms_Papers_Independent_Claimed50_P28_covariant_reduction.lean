-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_covariant_reduction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.covariant_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:16:57.41929+00:00
-- url     : https://prove2.me/theorems/df18c546-0a38-48fd-920b-e5fa6bca4934
-- title:
--   Covariant replacement preserves transported-dual loss
-- statement:
--   Fix $d\ge1$, identity representation, prior mean $I/d$, and one of the operation, channel or unital target spans. Let $(\Pi_x,\Delta_x)$ be any finite-loss physical tester and unbiased reconstruction dual on that span. With independent probability Haar variables $U,V\in SU(d)$, set $\Pi_{x,U,V}=(U\otimes V)\Pi_x(U\otimes V)^\dagger$ and transport $\Delta_x$ by the same conjugation. The transported family is again an admissible tester and dual, and
--
--   $$\eta(\Pi_{x,U,V},\Delta_{x,U,V})=\eta(\Pi_x,\Delta_x),\qquad \int\Pi_{x,U,V}=I/d.$$
--
--   The normalized input may therefore be chosen as $|I\rangle\!\rangle/\sqrt d$. The physical output POVM density is $d\Pi_{x,U,V}$, and applying the induced-tester contraction to it yields $\Pi_{x,U,V}$. An admissible dual for the new tester has loss no greater than the original loss; in particular the transported dual already has equal loss. This reduction uses continuous Haar outcomes and preserves completeness on the selected invariant target span.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 2, (22)–(25)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF pp.2–3, (22)–(25): Haar covariant replacement transports a dual with equal eta.
Reoptimizing the transported dual may improve it. The new preparation is |I>>/sqrt(d),
and the physical measurement density is d Pi. -/
theorem covariant_reduction {d : ℕ} (hd : 0 < d) (K : TomographyDomain)
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (P D : X → Op (ChoiBasis d)) (h : TomographyAdmissible mu P D K) :
    let nu := mu.prod (haar.prod haar)
    TomographyAdmissible nu (covariant P) (covariant D) K ∧
    eta K nu (covariant P) (covariant D) = eta K mu P D ∧
    (∫ z, covariant P z ∂nu) = ((d : ℂ)⁻¹) • (1 : Op (ChoiBasis d)) ∧
    QAlgorithms.IsDensityMatrix (maximallyEntangledDensity d) ∧
    IsPOVMDensity nu (fun z => (d : ℂ) • covariant P z) ∧
    (∀ z, inducedTester (maximallyEntangledDensity d) ((d : ℂ) • covariant P z) =
      covariant P z) ∧
    ∃ E : X × GroupPair d → Op (ChoiBasis d), TomographyAdmissible nu (covariant P) E K ∧
      eta K nu (covariant P) E ≤ eta K mu P D := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
