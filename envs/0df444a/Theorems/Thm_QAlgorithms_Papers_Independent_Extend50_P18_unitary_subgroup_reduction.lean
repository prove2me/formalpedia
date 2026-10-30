-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P18_unitary_subgroup_reduction
-- name    : QAlgorithms.Papers.Independent.Extend50.P18.unitary_subgroup_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:01:39.700524+00:00
-- url     : https://prove2.me/theorems/4c3a478e-f202-4ea2-bde1-dcc0565b9963
-- title:
--   Unnumbered §VI-B: unitary subgroup reduction (PRIR)
-- statement:
--   Let $H\le S_n$ be any subgroup and let $\rho$ be a finite-dimensional unitary irreducible representation of $S_n$ on $\mathbb C^m$, $m>0$. There are finitely many pairwise inequivalent unitary irreducible representations $\varphi^\alpha$ of $H$, positive multiplicities $c_\alpha$, and one unitary coordinate transformation $U$ such that
--
--   $$
--   U^\dagger\rho(h)U=\bigoplus_\alpha\left(I_{c_\alpha}\otimes\varphi^\alpha(h)\right)\qquad(h\in H).
--   $$
--
--   Both $U^\dagger U$ and $UU^\dagger$ are the corresponding identities. Repeated copies use the same fixed matrix realization. This supplies partial reduction for arbitrary subgroups; Young-path labels are reserved for the symmetric-group tower.
-- source:
--   Efficient multi port-based teleportation schemes, arXiv:2008.00984v4, PDF p. 11, Unnumbered §VI-B

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P18

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P18

attribute [local instance] Classical.propDecidable

/-- Unnumbered PRIR existence: arbitrary subgroup, finite multiplicities,
one simultaneous unitary change of basis, and fixed realizations for repeated
H-irreps. No Young paths are attributed to arbitrary H (PDF p.11, (60)). -/
theorem unitary_subgroup_reduction (n m : ℕ) (H : Subgroup (Equiv.Perm (Fin n)))
    (rho : FiniteUnitaryRepresentation (Equiv.Perm (Fin n)) m) (hirr : MatrixIrreducible rho) :
    ∃ (a : ℕ) (dims copies : Fin a → ℕ) (reps : (label : Fin a) → FiniteUnitaryRepresentation H (dims label)),
      (∀ label, 0 < copies label ∧ MatrixIrreducible (reps label)) ∧
      (∀ label other, label ≠ other →
        ∀ T : Matrix (Fin (dims other)) (Fin (dims label)) ℂ,
          (∀ h, T * (reps label).matrix h = (reps other).matrix h * T) → T = 0) ∧
      ∃ U : Matrix (Fin m) (SubgroupBlockIndex dims copies) ℂ,
        Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
          ∀ h : H, Uᴴ * rho.matrix h.val * U = subgroupBlockMatrix dims copies reps h := by sorry

end QAlgorithms.Papers.Independent.Extend50.P18

end
