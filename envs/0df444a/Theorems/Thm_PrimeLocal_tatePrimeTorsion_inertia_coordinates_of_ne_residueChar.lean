-- Prove2me | Theorems.Thm_PrimeLocal_tatePrimeTorsion_inertia_coordinates_of_ne_residueChar
-- name    : PrimeLocal.tatePrimeTorsion_inertia_coordinates_of_ne_residueChar
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:02:45.032508+00:00
-- url     : https://prove2.me/theorems/e17353fd-5a44-4277-a13e-51aa940a7e87
-- title:
--   Inertia on p-torsion of a Tate curve, p different from q
-- statement:
--   For a Tate curve over Q_q and a prime p >= 5 different from q, the p-torsion has coordinates (i, j) in which every inertia element acts by (i, j) -> (i + c j, j).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_TateCurve_TorsionParametrization
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine TateCurve

namespace PrimeLocal
theorem tatePrimeTorsion_inertia_coordinates_of_ne_residueChar (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ≠ q) (qT : ℚ_[q]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1) : letI : DecidableEq (AlgebraicClosure ℚ_[q]) := Classical.decEq _; ∃ (ζ t : AlgebraicClosure ℚ_[q]), IsPrimitiveRoot ζ p ∧ t ^ p = algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]) qT ∧ ∃ φ : (ZMod p × ZMod p) ≃ Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[q])).Point p, (∀ a b, (φ (a + b) : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[q])).Point) = φ a + φ b) ∧ ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, (∀ x : PadicAlgCl q, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → ∃ c : ℕ, ∀ i j : ZMod p, σ • (φ (i, j)) = φ (i + c • j, j) := by sorry
end PrimeLocal
