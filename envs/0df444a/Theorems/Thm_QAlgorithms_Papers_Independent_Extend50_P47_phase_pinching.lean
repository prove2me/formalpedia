-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_phase_pinching
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.phase_pinching
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:35:01.023466+00:00
-- url     : https://prove2.me/theorems/176756ef-1aa8-40e6-9b77-14e254a04092
-- title:
--   Collective dephasing is weight pinching, (197)–(202)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity.
--
--   For all n≥0 and every operator ρ, the normalized collective phase conjugation integral is Σk=0^n PkρPk, retaining exactly those matrix entries with equal input/output Hamming weights. A density matrix is invariant iff it equals this pinching.
--
--   $$
--   \mathcal C_z^{(n)}(X)=\sum_{k=0}^nP_kXP_k,\qquad\mathcal C_z^{(n)}(\rho)=\rho\iff\rho_{xy}=0\text{ when }H(x)\ne H(y).
--   $$
--
--   $X$ is any operator, $\rho$ is a density, $H$ denotes Hamming weight, and $\mathcal C_z^{(n)}$ is the normalized continuous conjugation integral over $[0,4\pi]$.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 27, Collective dephasing is weight pinching, (197)–(202)

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

/-- PDF pp.27–28, (197)–(202): collective dephasing is pinching in all weight
blocks, and its fixed states are block diagonal, not necessarily single-sector. -/
theorem phase_pinching (n : ℕ) :
    (∀ rho : Mat (Qubits n), collectiveZTwirl n rho =
      ∑ k : Fin (n + 1), weightProjector n k.val * rho * weightProjector n k.val) ∧
    (∀ rho : Mat (Qubits n), IsDensityMatrix rho →
      (collectiveZTwirl n rho = rho ↔ ∀ x y, bitHammingWeight x ≠ bitHammingWeight y → rho x y = 0)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
