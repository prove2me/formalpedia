-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_symmetrySubsets_viable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.symmetrySubsets_viable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:47:14.266726+00:00
-- url     : https://prove2.me/theorems/f69124c2-affd-4b67-8bd2-2ce4591816cd
-- title:
--   Remark 3.7: viable symmetry subsets
-- statement:
--   For a GKSL reduced system on $\mathbb C^n$, $n\ge2$, every degeneracy plane, meaning the fixed-point set of any coordinate-permutation subgroup intersected with the simplex, is viable for (C). Moreover,
--
--   $$\Delta^{n-1}_{\downarrow}\text{ and every coordinate permutation of }\Delta^{n-1}_{\downarrow}\text{ are viable for (C)}.$$
--
--   Viability means that from every point there is an all-time relaxed trajectory staying in the specified set. No unrestricted affine plane is declared viable.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 10, Remark 3.7: viable symmetry subsets

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.10, Remark 3.7: viable symmetry subsets.  -/
theorem symmetrySubsets_viable {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    (∀ H : Subgroup (Equiv.Perm (Fin n)),
      viable D {x | x ∈ simplex n ∧ ∀ p ∈ H, ∀ i, x (p i) = x i}) ∧
    viable D (chamber n) ∧
    (∀ p : Equiv.Perm (Fin n), viable D {x | ∃ y ∈ chamber n, x = fun i => y (p i)}) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
