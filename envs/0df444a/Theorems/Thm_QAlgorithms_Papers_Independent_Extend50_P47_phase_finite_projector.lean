-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_phase_finite_projector
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.phase_finite_projector
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:34:22.194338+00:00
-- url     : https://prove2.me/theorems/6d0d58ee-32cb-40ca-a7d7-1bf7419ebb80
-- title:
--   Finite collective-phase projector formula, (182)–(189)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity.
--
--   For all n≥0, define exactly Uy=Σx=0^n exp(πi(2y-n)(2x-n)/(n+1))Px for 0≤y≤n; each is unitary and (n+1)⁻¹Σy Uy is the collective-phase Bose projector. The associated uniform controlled-unitary projection test has the same acceptance.
--
--   $$
--   U_y=\sum_{x=0}^n e^{\pi i(2y-n)(2x-n)/(n+1)}P_x,\quad U_y^\dagger U_y=I,\quad\frac1{n+1}\sum_{y=0}^nU_y=\Pi_z^{(n)}.
--   $$
--
--   $P_x$ projects onto weight $x$, $0\le y\le n$, and $n\ge0$. Equality of the raw averages gives equality of the two control-return acceptance probabilities, without asserting a group law for the finite family.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 27, Finite collective-phase projector formula, (182)–(189)

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

/-- PDF pp.26–27, (182)–(189): the n+1 finite unitaries have precisely the
continuous raw average, hence exactly the same control-return acceptance.
The finite family need not be a group for odd n. -/
theorem phase_finite_projector (n : ℕ) :
    (∀ y, finitePhase n y ∈ Matrix.unitaryGroup (Qubits n) ℂ) ∧
    symmetryControlAverage (finitePhase n) = collectiveZAverage n ∧
    ∀ rho : Mat (Qubits n), IsDensityMatrix rho →
      controlReturnProbability (symmetryControlAverage (finitePhase n)) rho = controlReturnProbability (collectiveZAverage n) rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
