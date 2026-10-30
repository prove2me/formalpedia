-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_equispaced_energy_universality
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.equispaced_energy_universality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:12:05.072543+00:00
-- url     : https://prove2.me/theorems/d8a1c809-3f69-4cd9-be3d-1a1fede9594f
-- title:
--   Theorem 14: heterogeneous equally spaced energy systems
-- statement:
--   Let n≥1 finite-dimensional systems have arbitrary positive local dimensions. At site j, allow any positive degeneracy at each energy ε_j+mΔE for 0≤m≤L_j, where ΔE>0 is common and ε_j is an arbitrary offset. The endpoint intrinsic energy is the sum of these local energies. Every unitary V commuting with this energy admits an exact finite-product W of two-local total-energy-conserving unitaries on the systems and one ancillary qubit of gap ΔE, such that
--
--   $$W(|\psi\rangle|0\rangle_a)=(V|\psi\rangle)|0\rangle_a\quad\forall\psi.$$
--
--   The same ancilla returns for every input. This permits unequal dimensions and degeneracies, as the informal theorem and G.3 specify.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 5, Theorem 14 (informal; also main-text thermodynamics theorem)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.5–6,40, Theorem 14: differing local dimensions and degeneracies
are permitted, as stated in G.3. One exact returned qubit suffices; no efficiency
or gate-count asymptotic is asserted. -/
theorem equispaced_energy_universality {n : ℕ} {D : Fin n → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Nonempty (D j)]
    (hn : 1 ≤ n) (e : EquispacedLevels D) (gap : ℝ) (hGap : 0 < gap)
    (V : Mat (SiteBasis D)) (hV : V ∈ Matrix.unitaryGroup (SiteBasis D) ℂ)
    (hComm : V * e.energy gap = e.energy gap * V) :
    ∃ W : Mat (SiteBasis D × Bool),
      W ∈ Submonoid.closure (heterogeneousEnergyGates (attachEnergy (e.energy gap) gap)) ∧
      HamiltonianLift W V := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
