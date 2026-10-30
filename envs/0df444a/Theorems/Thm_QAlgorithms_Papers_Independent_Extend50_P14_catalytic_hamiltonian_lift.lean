-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_catalytic_hamiltonian_lift
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.catalytic_hamiltonian_lift
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:14:12.763989+00:00
-- url     : https://prove2.me/theorems/68b111db-93bf-4ff8-8c41-4ce7bb1a4534
-- title:
--   Lemma 6: catalytic Hamiltonian lift with specified controls
-- statement:
--   Let n,d≥1 and ΔE>0. Each d-dimensional site has levels rΔE, 0≤r<d; write H_intr for their additive energy. If H is Hermitian and commutes with H_intr, there exists a Hermitian K on the system and a two-level ancilla such that
--
--   $$iK\in\operatorname{Lie}_{\mathbb R}\{iZ_a,\ iR_{j,a}^{(l)},\ iR_{j,j+1}^{(l,l')}\},\qquad K(|\psi\rangle|0\rangle_a)=(H|\psi\rangle)|0\rangle_a.$$
--
--   The transfer controls are those of G10: 1≤l,l'<d; ancilla couplings use every 1≤j≤n and chain couplings only 1≤j<n. The same lift works for every system vector.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 44, Lemma 6: catalytic Hamiltonian lift with specified controls

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.44, Lemma 6: the Hamiltonian lift is an output, never an input assumption.
Printed G12 gives a common j=1,...,n range; use j<n for system-chain edges and
j<=n for ancilla couplings, exactly the separate ranges defining these operators
in G10. No other control or conclusion is changed. -/
theorem catalytic_hamiltonian_lift (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (gap : ℝ) (hGap : 0 < gap) (H : EMat n d) (hH : H.IsHermitian)
    (hComm : H * intrinsicEnergy n d gap = intrinsicEnergy n d gap * H) :
    ∃ K : Mat (EnergyBasis n d × Bool), K.IsHermitian ∧ Complex.I • K ∈ energyLie n d ∧
      HamiltonianLift K H := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
