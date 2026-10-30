-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_diagonal_catalytic_lift
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.diagonal_catalytic_lift
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:16:20.15671+00:00
-- url     : https://prove2.me/theorems/03fdcb5e-d3aa-4198-9cbf-3ded6fc5413c
-- title:
--   Lemma 7: diagonal catalytic Hamiltonian lift
-- statement:
--   Let n,d≥1. For every Hermitian H diagonal in the physical product-energy basis there is a Hermitian K on the system and one ground-state qubit such that
--
--   $$iK\in\operatorname{Lie}_{\mathbb R}\{iZ_a,\ iR_{j,a}^{(l)},\ iR_{s,s+1}^{(l,l')}\},\qquad K(|\psi\rangle|0\rangle_a)=(H|\psi\rangle)|0\rangle_a\quad\forall\psi.$$
--
--   Here 1≤l,l'<d, 1≤j≤n and 1≤s<n, and the transfer matrices are exactly G10. The conclusion concerns the full qudit space and assumes none of the faulty embedded-qubit identities in the proof.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 47, Lemma 7: diagonal catalytic Hamiltonian lift

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.47–49, Lemma 7/G30: all diagonal Hermitian matrices, without
assuming the false embedded-qubit identities G43–G49 as hypotheses. -/
theorem diagonal_catalytic_lift (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (H : EMat n d) (hH : H.IsHermitian) (hDiag : Matrix.IsDiag H) :
    ∃ K : Mat (EnergyBasis n d × Bool), K.IsHermitian ∧ Complex.I • K ∈ energyLie n d ∧
      HamiltonianLift K H := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
