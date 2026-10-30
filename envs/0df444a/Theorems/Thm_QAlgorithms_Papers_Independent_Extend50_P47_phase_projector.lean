-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_phase_projector
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.phase_projector
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:33:27.528533+00:00
-- url     : https://prove2.me/theorems/9d3b8548-8c5a-4547-a856-168e48547704
-- title:
--   Collective-phase Bose projector, (174)–(181)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity.
--
--   For all n≥0, define the normalized integral (1/4π)∫0^4π Rz(φ)^⊗n dφ. It equals the diagonal projector onto weight n/2 if n is even and zero if n is odd; for n=2 it is |01⟩⟨01|+|10⟩⟨10|. Bose-symmetric density states exist only in the even case and have this support.
--
--   $$
--   \Pi_z^{(n)}=\frac1{4\pi}\int_0^{4\pi}R_z(\phi)^{\otimes n}\,d\phi=\begin{cases}P_k,&n=2k,\\0,&n\text{ odd}.\end{cases}
--   $$
--
--   $R_z(\phi)=\operatorname{diag}(e^{-i\phi/2},e^{i\phi/2})$ and $P_k$ projects onto all bit strings of Hamming weight $k$. The scalar $n=0$ case gives the identity.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 26, Collective-phase Bose projector, (174)–(181)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.su2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.su2BorelSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.u2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.u2BorelSpace

/-- PDF pp.25–27, (174)–(180). Source correction to the prose after (189):
when n=2k the weight is k. At n=0 the scalar projector is the identity. -/
theorem phase_projector (n : ℕ) :
    (∀ k, n = 2 * k → collectiveZAverage n = weightProjector n k) ∧
    (Odd n → collectiveZAverage n = 0) ∧
    (∀ rho : Mat (Qubits n), IsDensityMatrix rho →
      (Bose (collectiveZAverage n) rho ↔ Even n ∧
        rho = weightProjector n (n / 2) * rho * weightProjector n (n / 2))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
