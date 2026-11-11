-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P36_lhs_invariant
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P36.lhs_invariant
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T08:19:52.361714+00:00
-- url     : https://prove2.me/theorems/9dcd1149-a629-4d0d-bfb1-e8f05f15f3d7
-- title:
--   Bob-to-Alice 1W-LOCC preserves unsteerability
-- statement:
--   Let \(\rho=(\rho_{a|x})\) be a no-signaling assemblage of positive operators on a finite-dimensional complex Hilbert space, with positive finite input and output alphabets and common trace \(t\in[0,1]\). Suppose \(\rho\) admits a local-hidden-state model of total mass \(t\). Let \(M\) be any Bob-to-Alice stochastic one-way LOCC: Bob applies a Kraus subinstrument, communicates its outcome to Alice, and Alice applies normalized input and output probability kernels. Source and target dimensions and alphabets may differ. Then
--
--   $$
--   \rho\in\mathrm{LHS}\quad\Longrightarrow\quad M(\rho)\in\mathrm{LHS}.
--   $$
--
--   If \(p=\operatorname{Tr}M(\rho)>0\), the conditional assemblage \(M(\rho)/p\) is normalized and also admits an LHS model. This identifies the free operations of the resource theory, including selective operations and the zero operation.
-- source:
--   The resource theory of steering, arXiv:1409.5804v3, PDF p. 4, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P36

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P36

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable

variable {d r s df rf sf m : ℕ}

/-- Theorem 1, PDF p.4; proof p.10. Subnormalized LHS outputs retain their assemblageMass.
Correction to Appendix B's word "normalized": only positive-success outputs
are renormalized. The zero operation produces the zero free assemblage. -/
theorem lhs_invariant (P : SteeringProtocol d r s df rf sf m) (rho : AssemblageBlocks d r s)
    (hrho : HasFiniteLHSModel rho) :
    HasFiniteLHSModel (protocolAction P rho) ∧
    (0 < assemblageMass (protocolAction P rho) →
      IsNormalized (normalizeAssemblage (protocolAction P rho)) ∧
      HasFiniteLHSModel (normalizeAssemblage (protocolAction P rho))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P36

end
