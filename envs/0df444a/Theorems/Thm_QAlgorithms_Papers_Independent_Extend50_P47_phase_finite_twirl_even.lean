-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_phase_finite_twirl_even
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.phase_finite_twirl_even
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:35:41.730381+00:00
-- url     : https://prove2.me/theorems/7aca1a4d-3fc6-4d88-9f18-0dd6f82a0646
-- title:
--   Valid even-n finite phase twirl, including the implemented n=2 case
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity.
--
--   For every even n (including zero), the literal Uy in (183) obey (n+1)⁻¹Σy UyρUy†=Σk PkρPk. In particular the n=2 gates U0=Rz(2π/3)^⊗2,U1=I,U2=U0† used by Figure 21 give the advertised collective symmetry test.
--
--   $$
--   \mathcal C_z^{(n)}(X)=\frac1{n+1}\sum_{y=0}^nU_yXU_y^\dagger\qquad(n\text{ even}).
--   $$
--
--   $X$ is any operator and $U_y=\sum_{x=0}^n e^{\pi i(2y-n)(2x-n)/(n+1)}P_x$ is the literal family of (183). This is an explicitly corrected even-$n$ specialization, including $n=0,2$.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 28, Valid even-n finite phase twirl, including the implemented n=2 case

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

/-- PDF pp.27–28, corrected even-n specialization of (206)–(208).
The unrestricted printed assertion is separately deferred: at odd n its
frequencies alias. Even n includes the implemented n=2 example and n=0. -/
theorem phase_finite_twirl_even (n : ℕ) (hn : Even n)
    (rho : Mat (Qubits n)) :
    collectiveZTwirl n rho = (n + 1 : ℂ)⁻¹ •
      ∑ y : Fin (n + 1), finitePhase n y * rho * (finitePhase n y)ᴴ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
