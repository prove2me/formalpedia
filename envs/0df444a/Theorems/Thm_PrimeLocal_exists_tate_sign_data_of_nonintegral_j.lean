-- Prove2me | Theorems.Thm_PrimeLocal_exists_tate_sign_data_of_nonintegral_j
-- name    : PrimeLocal.exists_tate_sign_data_of_nonintegral_j
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:58:52.977045+00:00
-- url     : https://prove2.me/theorems/27398ee6-35c5-4dc4-8fc8-5a909bd06e73
-- title:
--   Tate parameter and quadratic sign data for non-integral j
-- statement:
--   If the j-invariant is not q-integral, the curve becomes isomorphic over an algebraic closure of Q_q to a Tate curve with parameter qT (0 < |qT| < 1), via a change of variables C whose Galois behaviour is governed by a square root s of an element d of Q_q: Galois elements fixing s fix C, the others change C by the negation automorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_TateCurve_TateParameter

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal

namespace PrimeLocal
theorem exists_tate_sign_data_of_nonintegral_j (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (q : ℕ) [Fact q.Prime] (hj : ¬ ((q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3)) : ∃ (qT : ℚ_[q]) (_ : qT ≠ 0) (_ : ‖qT‖₊ < 1) (d : ℚ_[q]) (s : AlgebraicClosure ℚ_[q]) (C : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ_[q])), s ^ 2 = algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]) d ∧ C • ((W.map (Int.castRingHom ℚ_[q])).map (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]))) = (TateCurve.curve qT).map (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])) ∧ ∀ σ : AlgebraicClosure ℚ_[q] ≃ₐ[ℚ_[q]] AlgebraicClosure ℚ_[q], (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧ (σ s ≠ s → C.map σ.toAlgHom.toRingHom = (⟨-1, 0, -1, 0⟩ : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ_[q])) * C) := by sorry
end PrimeLocal
